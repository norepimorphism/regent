// SPDX-License-Identifier: MPL-2.0

//! Procedural macros for [*regent*].
//!
//! [regent]: https://crates.io/crates/regent

use proc_macro::TokenStream;
use quote::{
    __private::{Span as Span2, TokenStream as TokenStream2},
    format_ident,
    quote,
    ToTokens as _,
};

/// Like [`try`](core::try) except the return type of the containing function is `T` instead of
/// [`Result<T, E>`](core::result::Result).
macro_rules! unwrap {
    ($expr:expr) => {
        match $expr {
            Ok(it) => it,
            Err(e) => {
                return e;
            }
        }
    };
}

/// Returns from the current function with a [`TokenStream`] generated by [`make_error`].
macro_rules! fail {
    ($span:expr, $msg:expr $(,)?) => {{
        return make_error($span, $msg);
    }};
}

/// Creates a [`TokenStream`] representing a compilation error with the given message.
fn make_error(span: Span2, msg: &'static str) -> TokenStream {
    syn::Error::new(span, msg).into_compile_error().into()
}

/// The whole point.
#[proc_macro_attribute]
pub fn bitwise(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let syn::ItemStruct {
        attrs: item_attrs,
        fields: item_fields,
        generics: item_generics,
        ident: item_ident,
        struct_token: item_struct,
        vis: item_vis,
        ..
    } = syn::parse_macro_input!(item as _);
    // This is a 'fallback span' for when a more precise span is unavailable.
    let item_span = item_struct.span;

    if !item_generics.params.is_empty() {
        fail!(item_span, "generic parameters are not supported");
    }

    // This snippet is prepended to the body of all functions we generate that rely on
    // `Bitwise::REPR_WIDTH` and `Bitwise::Repr`.
    let fn_prelude = quote! {
        const ITEM_REPR_WIDTH: usize = <#item_ident as ::regent::Bitwise>::REPR_WIDTH;
        type ItemRepr = <#item_ident as ::regent::Bitwise>::Repr;
    };

    // This is the total bit width of all fields.
    let mut item_width: usize = 0;
    // This is a list of methods (or pairs of methods) we generate for `#item_ident`.
    //
    // Specifically, each element is a pair of getter and setter methods for a particular field of
    // `#item_ident`.
    let mut item_fns = Vec::new();
    // This is a list of all arguments accepted by `#item_ident::new`.
    //
    // These arguments map one-to-one to the fields of `#item_ident`.
    let mut item_new_args = Vec::new();
    // This is a list of statements (or series of statements) that process the arguments of
    // `#item_ident::new`.
    let mut item_new_stmts = Vec::new();

    // Process fields.
    for field in item_fields {
        let syn::Field {
            attrs: field_attrs, ident: field_ident, ty: field_ty, vis: field_vis, ..
        } = field;

        let Some(field_ident) = field_ident else {
            fail!(item_span, "tuple structs are not supported");
        };
        let field_span = field_ident.span();

        if !field_attrs.is_empty() {
            fail!(field_span, "attributes are not (yet) supported on struct fields");
        }

        let field_ty = unwrap!(Type::parse(field_span, &field_ty));
        match field_ty {
            Type::Tuple(ref tys) => if tys.is_empty() {
                fail!(field_span, "struct fields cannot be the unit type")
            },
            Type::Array { len, .. } => if len == 0 {
                fail!(field_span, "struct fields cannot be zero-sized arrays")
            },
            _ => {}
        }

        let field_width = field_ty.width();

        let field_getter_glue =
            field_ty.field_getter_glue(quote!(field), quote!(field_as_repr), field_width);
        let field_setter_glue =
            field_ty.field_setter_glue(quote!(field), quote!(field_as_repr), field_width);
        let new_glue = field_ty.field_setter_glue(
            field_ident.to_token_stream(),
            quote!(field_as_repr),
            field_width,
        );

        // This is a type used to represent this field in arguments and return types.
        let field_ty = field_ty.as_rust_primitives();
        if !field_ty.exists() {
            fail!(field_span, "this field cannot be represented by any primitive integer type");
        }

        // This is the position of the least-significant bit of this field.
        let field_offset = item_width;
        let field_getter_ident = quote!(#field_ident);
        let field_setter_ident = format_ident!("set_{field_ident}");

        item_width += field_width;
        item_fns.push(quote! {
            #field_vis fn #field_getter_ident(&self) -> #field_ty {
                #fn_prelude

                let mut field: #field_ty;
                let mut field_as_repr = self.0 >> #field_offset;
                #field_getter_glue

                field
            }

            #field_vis fn #field_setter_ident(&mut self, field: #field_ty) {
                #fn_prelude

                let mut field_as_repr: ItemRepr;
                #field_setter_glue

                self.0 &= !((!0 >> (ITEM_REPR_WIDTH - #field_width)) << #field_offset);
                self.0 |= field_as_repr << #field_offset;
            }
        });
        item_new_args.push(quote!(#field_ident: #field_ty));
        item_new_stmts.push(quote! {
            bits <<= #field_width;
            let mut field_as_repr: ItemRepr;
            #new_glue
            bits |= field_as_repr;
        });
    }
    item_new_stmts.reverse();

    let item_repr = UIntType { width: item_width }.round_up();
    if !item_repr.exists() {
        fail!(item_span, "this struct cannot be represented by any primitive integer type");
    }

    quote! {
        #(#item_attrs)*
        #[repr(transparent)]
        #item_vis struct #item_ident(#item_repr);

        impl #item_ident {
            #item_vis fn new(#(#item_new_args),*) -> Self {
                #fn_prelude

                let mut bits: ItemRepr = 0;
                #(#item_new_stmts)*

                Self(bits)
            }

            #(#item_fns)*
        }

        impl ::regent::Bitwise for #item_ident {
            const WIDTH: usize = #item_width;

            type Repr = #item_repr;
        }

        impl From<#item_repr> for #item_ident {
            fn from(repr: #item_repr) -> #item_ident {
                #item_ident(repr)
            }
        }

        impl From<#item_ident> for #item_repr {
            fn from(it: #item_ident) -> #item_repr {
                it.0
            }
        }
    }
    .into()
}

/// The type of a field.
enum Type {
    /// A [prime type](PrimeType).
    Prime(PrimeType),
    /// A tuple of [prime types](PrimeType).
    Tuple(Vec<PrimeType>),
    /// An array of [prime types](PrimeType).
    Array {
        /// The element type.
        ty: PrimeType,
        /// The number of elements.
        len: usize,
    },
}

impl Type {
    fn parse(span: Span2, ty: &syn::Type) -> Result<Self, TokenStream> {
        match ty {
            syn::Type::Path(ty) => PrimeType::parse(span, ty).map(Self::Prime),
            syn::Type::Tuple(syn::TypeTuple { elems: tys, .. }) => {
                let tys = tys
                    .iter()
                    .map(|ty| {
                        if let syn::Type::Path(ty) = ty {
                            PrimeType::parse(span, ty)
                        } else {
                            Err(make_error(span, "tuple element type must be a path"))
                        }
                    })
                    .collect::<Result<Vec<PrimeType>, _>>()?;

                Ok(Self::Tuple(tys))
            }
            syn::Type::Array(syn::TypeArray { elem: ty, len, .. }) => {
                let syn::Type::Path(ref ty) = **ty else {
                    return Err(make_error(span, "array element type must be a path"));
                };
                let ty = PrimeType::parse(span, ty)?;
                let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(len), .. }) = len else {
                    return Err(make_error(span, "array length must be an integer literal"));
                };
                let len =
                    len.base10_parse().map_err(|e| TokenStream::from(e.into_compile_error()))?;

                Ok(Self::Array { ty, len })
            }
            _ => Err(make_error(span, "the type of this field is not supported")),
        }
    }

    fn as_rust_primitives(&self) -> Self {
        match self {
            Self::Prime(ty) => Self::Prime(ty.as_rust_primitive()),
            Self::Tuple(tys) => Self::Tuple(tys.iter().map(|it| it.as_rust_primitive()).collect()),
            Self::Array { ty, len } => Self::Array { ty: ty.as_rust_primitive(), len: *len },
        }
    }

    fn exists(&self) -> bool {
        match self {
            Self::Prime(ty) => ty.exists(),
            Self::Tuple(tys) => tys.iter().all(|it| it.exists()),
            Self::Array { ty, .. } => ty.exists(),
        }
    }

    fn width(&self) -> usize {
        match self {
            Self::Prime(ty) => ty.width(),
            Self::Tuple(tys) => tys.iter().map(|ty| ty.width()).sum(),
            Self::Array { ty, len } => ty.width() * len,
        }
    }

    fn field_getter_glue(
        &self,
        field: TokenStream2,
        field_as_repr: TokenStream2,
        field_width: usize,
    ) -> TokenStream2 {
        match self {
            Self::Prime(ty) => ty.field_getter_glue(field, field_as_repr, field_width),
            Self::Tuple(tys) => {
                let mut tmp_elems = Vec::new();
                for ty in tys.iter().rev() {
                    let elem_width = ty.width();
                    let elem_getter_glue =
                        ty.field_getter_glue(quote!(elem), field_as_repr.clone(), elem_width);
                    tmp_elems.push(quote!({
                        let elem;
                        #elem_getter_glue
                        #field_as_repr >>= #elem_width;

                        elem
                    }));
                }
                let mut elems = Vec::new();
                for i in (0..tys.len()).rev() {
                    let i = syn::Index::from(i);
                    elems.push(quote!(tmp.#i));
                }

                quote! {
                    #field = {
                        let tmp = (#(#tmp_elems),*);

                        (#(#elems),*)
                    };
                }
            }
            Self::Array { ty, len } => {
                let elem_width = ty.width();
                let elem_getter_glue = ty.field_getter_glue(quote!(elem), field_as_repr.clone(), elem_width);

                let mut elems = Vec::new();
                for _ in 0..(*len) {
                    elems.push(quote! { get_elem() });
                }

                quote! {
                    let mut get_elem = || {
                        let elem;
                        #elem_getter_glue
                        #field_as_repr >>= #elem_width;

                        elem
                    };
                    #field = [#(#elems),*];
                }
            }
        }
    }

    fn field_setter_glue(
        &self,
        field: TokenStream2,
        field_as_repr: TokenStream2,
        field_width: usize,
    ) -> TokenStream2 {
        match self {
            Self::Prime(ty) => ty.field_setter_glue(field, field_as_repr, field_width),
            Self::Tuple(tys) => {
                let mut result = quote! { #field_as_repr = 0; };
                for (i, ty) in tys.iter().enumerate() {
                    let i = syn::Index::from(i);
                    let elem_width = ty.width();
                    let elem_getter_glue =
                        ty.field_setter_glue(quote!(#field.#i), field_as_repr.clone(), elem_width);
                    result.extend(quote! {
                        #elem_getter_glue
                        #field_as_repr <<= #elem_width;
                    });
                }

                result
            }
            Self::Array { ty, len } => {
                let elem_width = ty.width();
                let elem_getter_glue =
                    ty.field_setter_glue(quote!(#field[i]), field_as_repr.clone(), elem_width);

                quote! {
                    field_as_repr = 0;
                    for i in 0..#len {
                        #elem_getter_glue
                        #field_as_repr <<= #elem_width;
                    }
                }
            }
        }
    }
}

impl quote::ToTokens for Type {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            Self::Prime(ty) => {
                ty.to_tokens(tokens);
            }
            Self::Tuple(tys) => {
                tokens.extend(quote! { ( #(#tys),* ) });
            }
            Self::Array { ty, len } => {
                tokens.extend(quote! { [#ty; #len] });
            }
        }
    }
}

#[derive(Clone, Copy)]
enum PrimeType {
    Bool,
    UInt(UIntType),
}

impl PrimeType {
    fn parse(span: Span2, ty: &syn::TypePath) -> Result<Self, TokenStream> {
        if let Some(ty) = ty.path.get_ident().map(ToString::to_string) {
            if ty == "bool" {
                return Ok(Self::Bool);
            } else if let Some(("", width)) = ty.split_once("u") {
                return UIntType::parse(span, width).map(Self::UInt);
            }
        }

        Err(make_error(span, "the type of this field is not supported"))
    }

    fn as_rust_primitive(self) -> Self {
        match self {
            Self::UInt(ty) => Self::UInt(ty.round_up()),
            other => other,
        }
    }

    fn exists(self) -> bool {
        match self {
            Self::UInt(ty) => ty.exists(),
            _ => true,
        }
    }

    fn width(self) -> usize {
        match self {
            Self::Bool => 1,
            Self::UInt(ty) => ty.width,
        }
    }

    fn field_getter_glue(
        self,
        field: TokenStream2,
        field_as_repr: TokenStream2,
        field_width: usize,
    ) -> TokenStream2 {
        let inner = quote! { #field_as_repr & (!0 >> (ITEM_REPR_WIDTH - #field_width)) };
        let expr = match self {
            Self::Bool => quote! { (#inner) == 1 },
            Self::UInt(_) => quote! { (#inner) as _ },
        };

        quote! { #field = #expr; }
    }

    fn field_setter_glue(
        self,
        field: TokenStream2,
        field_as_repr: TokenStream2,
        field_width: usize,
    ) -> TokenStream2 {
        quote! {
            #field_as_repr |= (#field as ItemRepr) & (!0 >> (ITEM_REPR_WIDTH - #field_width));
        }
    }
}

impl quote::ToTokens for PrimeType {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match *self {
            Self::Bool => {
                tokens.extend(quote!(bool));
            }
            Self::UInt(ty) => {
                ty.to_tokens(tokens);
            }
        }
    }
}

#[derive(Clone, Copy)]
struct UIntType {
    width: usize,
}

impl UIntType {
    fn parse(span: Span2, width: &str) -> Result<Self, TokenStream> {
        let width = width.parse().map_err(|_| {
            make_error(span, "the type of this field has an invalid integer suffix")
        })?;
        if width == 0 {
            return Err(make_error(span, "this field is zero-sized, which is not supported"))?;
        }

        Ok(Self { width })
    }

    fn round_up(self) -> Self {
        let width = if self.width <= 8 {
            8
        } else {
            // This is the 'magnitude' of `width`, or the integer component of
            // `log2(width)`.
            let mag = self.width.ilog2() as usize;
            // This is the fractional component of `log2(width)`.
            let frac = self.width & ((1 << mag) - 1);

            if frac == 0 {
                self.width
            } else {
                1 << (mag + 1)
            }
        };

        Self { width }
    }

    fn exists(self) -> bool {
        match self.width {
            8 | 16 | 32 | 64 | 128 => true,
            _ => false,
        }
    }
}

impl quote::ToTokens for UIntType {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        tokens.extend(format_ident!("u{}", self.width).into_token_stream());
    }
}
