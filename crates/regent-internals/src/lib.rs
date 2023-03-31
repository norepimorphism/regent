// SPDX-License-Identifier: MPL-2.0

//! Procedural macros for [Regent].
//!
//! [Regent]: https://crates.io/crates/regent

///// PROGRAMMER'S NOTE ////////////////////////////////////////////////////////////////////////////
//
// Throughout *regent-internals*, we will distinguish between 'macro evaluation time' (when the
// entrypoint to a proc macro is invoked) and 'compile-time' (when the crate invoking a proc macro
// is fully-expanded) to explain the kinds of information knowable to [`bitwise`] and which must be
// supplied via other means, e.g., in attribute arguments.

use std::borrow::Cow;

use proc_macro::TokenStream;
use proc_macro2::{Span as Span2, TokenStream as TokenStream2};
use quote::{format_ident, quote, ToTokens};
use syn::{punctuated::Punctuated, spanned::Spanned as _};

///// UTILITY MACROS ///////////////////////////////////////////////////////////////////////////////

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

/// Creates a [`syn::Error`] with the given error message.
macro_rules! err {
    ($fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        err!([Span2::call_site()] $fmt $(, $fmt_arg)*)
    };
    ([ $span:expr ] $fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        syn::Error::new($span, format!($fmt $(, $fmt_arg)*))
    };
}

///// PUBLIC API ///////////////////////////////////////////////////////////////////////////////////

/// Does the thing.
///
/// See the [README] for usage information.
///
/// [README]: https://github.com/norepimorphism/regent/blob/main/README.md
#[proc_macro_attribute]
pub fn bitwise(args: TokenStream, item: TokenStream) -> TokenStream {
    #[derive(Default)]
    struct ItemArgs {
        size: Option<usize>,
        width: Option<usize>,
    }

    let mut item_args = ItemArgs::default();
    let item_args_parser = syn::meta::parser(|meta| {
        let ident = meta.path.get_ident().ok_or_else(|| {
            err!(
                "attribute argument path `{}` should be an identifier",
                meta.path.into_token_stream()
            )
        })?;
        let get_value = || -> Result<usize, _> {
            meta.value().and_then(|it| it.parse::<syn::LitInt>()).and_then(|it| it.base10_parse())
        };
        if ident == "size" {
            item_args.size = Some(get_value()?);
        } else if ident == "width" {
            item_args.width = Some(get_value()?);
        } else {
            return Err(err!("attribute argument `{ident}` is not supported"));
        }

        Ok(())
    });
    syn::parse_macro_input!(args with item_args_parser);
    if item_args.size.is_some() && item_args.width.is_some() {
        return err!("`size` and `width` attribute arguments are mutually exclusive")
            .into_compile_error()
            .into();
    }
    let expected_width = item_args.width.or_else(|| item_args.size.map(|it| it * 8));

    match syn::parse_macro_input!(item as _) {
        syn::Item::Enum(item) => bitwise_on_enum(expected_width, item),
        syn::Item::Struct(item) => bitwise_on_struct(expected_width, item),
        _ => err!("this kind of item is not supported").into_compile_error().into(),
    }
}

/// [`bitwise`] for enums.
fn bitwise_on_enum(expected_width: Option<usize>, item: syn::ItemEnum) -> TokenStream {
    check_generics(item.generics);
    let item_span = item.span();
    let syn::ItemEnum {
        attrs: mut item_attrs,
        generics: item_generics,
        ident: item_ident,
        enum_token: item_enum,
        variants: item_variants,
        vis: item_vis,
        ..
    } = item;

    let mut from_repr_checked_arms = Vec::new();
    let mut next_discrim = Width::Lit(0);
    for variant in item_variants.iter() {
        let variant_ident = &variant.ident;
        let variant_span = variant_ident.span();

        if !variant.fields.is_empty() {
            fail!(variant_span, "variant fields are not supported");
        }

        let variant_discrim = if let Some((_, discrim)) = &variant.discriminant {
            Width::Expr(discrim.clone())
        } else {
            next_discrim.clone()
        };
        from_repr_checked_arms.push(quote!(#variant_discrim => Some(Self::#variant_ident)));
        next_discrim = variant_discrim + Width::Lit(1);
    }

    let item_width = Width::Lit(match item_variants.len() {
        1 => 1,
        other if other.is_power_of_two() => other.ilog2() as _,
        other => (other.ilog2() + 1) as _,
    });

    let mut const_ctx = Vec::new();
    enforce_item_width!(expected_width, item_span, item_width, const_ctx);
    let item_repr =
        unwrap!(determine_item_repr(expected_width, item_span, &mut item_attrs, &item_width));
    item_attrs.push({
        let dont_care_span = Span2::call_site();

        syn::Attribute {
            pound_token: syn::Token![#](dont_care_span),
            style: syn::AttrStyle::Outer,
            bracket_token: syn::token::Bracket(dont_care_span),
            meta: syn::MetaList {
                path: syn::Ident::new("repr", dont_care_span).into(),
                delimiter: syn::MacroDelimiter::Paren(syn::token::Paren(dont_care_span)),
                tokens: item_repr.into_token_stream(),
            }
            .into(),
        }
    });

    let mut output = Item {
        attrs: item_attrs,
        vis: item_vis,
        token: quote!(enum),
        ident: item_ident,
        body: quote!({ #item_variants }),
        methods: Vec::new(),
        bitwise_impl: BitwiseImpl {
            width: item_width,
            repr: item_repr,
            from_repr_unchecked: quote! {
                // FIXME: is there a less 'wildly unsafe' version to this?
                ::core::mem::transmute(repr)
            },
            from_repr_checked: quote! {
                match repr as usize {
                    #(#from_repr_checked_arms,)*
                    _ => None,
                }
            },
            to_repr: quote! {
                // FIXME: is there an equivalent safe version?
                unsafe { *(self as *const Self as *const _) }
            },
        },
    }
    .into_token_stream();
    output.extend(prelude);

    output.into()
}

/// [`bitwise`] for structs.
fn bitwise_on_struct(expected_width: Option<usize>, item: syn::ItemStruct) -> TokenStream {
    check_generics(item.generics);
    let item_span = item.span();
    let syn::ItemStruct {
        attrs: mut item_attrs,
        fields: item_fields,
        ident: item_ident,
        struct_token: item_struct,
        vis: item_vis,
        ..
    } = item;

    // These next few variables are default-initialized for now and are continuously updated during
    // field processing.

    // This is the total bit-width of all fields.
    let mut item_width = Width::zero(item_span);
    // This is the list of `impl #item_ident` methods we generate.
    let mut item_methods = Vec::new();
    // This is the list of all arguments accepted by `#item_ident::new`.
    let mut item_new_args = Vec::new();
    // This is a list of 'snippets' (or series of statements) that initialize the fields in
    // `#item_ident::new`.
    let mut new_stmts = Vec::new();
    let mut from_repr_checked_body = TokenStream2::new();

    // Process fields.
    for (i, field) in item_fields.into_iter().enumerate() {
        trait Endec {
            /// Generates an expression that produces a value of this type from a representation.
            fn decode(&self, repr_width: &Width, repr: syn::Expr) -> TokenStream2;

            /// Generates an expression that produces a representation from a value of this type.
            fn encode(&self, repr_width: &Width, value: syn::Expr) -> TokenStream2;
        }

        impl Endec for Type {
            fn decode(&self, repr_width: &Width, repr: syn::Expr) -> TokenStream2 {
                match self {
                    Self::Prime(ty) => ty.decode(repr_width, repr),
                    Self::Tuple(tys) => {
                        // The strategy is to create a temporary tuple formed from block expressions
                        // that continuously bit-shift the next element to the bottom of `repr` and
                        // then feed those tuple elements, in reverse order, to another tuple.
                        // Reversal is necessary in this case because we take from the
                        // least-significant bits of `repr`, which represent the last tuple element.

                        let mut tmp_elems = Vec::new();
                        let tmp_elems = tys
                            .iter()
                            .rev()
                            .map(|ty| {
                                let elem_width = ty.width();
                                // Note: it's okay to reuse the field representation for individual
                                // elements because they are equal or lesser in width.
                                let elem = ty.decode(&elem_width, repr.clone());
                                let elem_width = elem_width.into_grouped_expr();

                                quote!({
                                    let elem = #elem;
                                    #repr >>= #elem_width;

                                    elem
                                })
                            })
                            .collect();
                        let elems = (0..tys.len())
                            .rev()
                            .map(|i| {
                                syn::ExprField {
                                    attrs: Vec::new(),
                                    base: Box::new(
                                        syn::ExprPath {
                                            attrs: Vec::new(),
                                            qself: None,
                                            // FIXME: span
                                            path: syn::Ident::new("tmp", Span2::call_site()).into(),
                                        }
                                        .into(),
                                    ),
                                    // FIXME: span
                                    dot_token: syn::Token![.](Span2::call_site()),
                                    member: syn::Member::Unnamed(i.into()),
                                }
                            })
                            .collect();

                        quote!({
                            let tmp = (#(#tmp_elems),*);

                            (#(#elems),*)
                        })
                    }
                    Self::Array { ty, len } => {
                        let elem_width = ty.width();
                        let elem = ty.decode(&elem_width, repr.clone());
                        let elem_width = elem_width.into_grouped_expr();

                        // We can make the generated code easier on the eyes with a closure.
                        let elems = (0..(*len))
                            .into_iter()
                            .map(|_| {
                                syn::ExprCall {
                                    attrs: Vec::new(),
                                    func: Box::new(
                                        syn::ExprPath {
                                            attrs: Vec::new(),
                                            qself: None,
                                            // FIXME: fix span
                                            path: syn::Ident::new("get_elem", Span2::call_site())
                                                .into(),
                                        }
                                        .into(),
                                    ),
                                    paren_token: Default::default(),
                                    args: Punctuated::new(),
                                }
                            })
                            .collect();

                        quote!({
                            let mut get_elem = || {
                                let elem = #elem;
                                #repr >>= #elem_width;

                                elem
                            };

                            [#(#elems),*]
                        })
                    }
                }
            }

            fn encode(&self, repr_width: &Width, value: syn::Expr) -> TokenStream2 {
                match self {
                    Self::Prime(ty) => ty.encode(repr_width, value),
                    Self::Tuple(tys) => {
                        let mut block_body = quote! { let mut result = 0; };
                        for (i, ty) in tys.iter().enumerate() {
                            let i = syn::Index::from(i);
                            let elem_width = ty.width();
                            let elem_encoded = ty.encode(quote!(#field.#i), &elem_width);
                            block_body.extend(quote! {
                                result <<= #elem_width;
                                result |= #elem_encoded;
                            });
                        }
                        block_body.extend(quote!(result));

                        quote!({ #block_body })
                    }
                    Self::Array { ty, len } => {
                        let elem_width = ty.width();
                        let elem_encoded = ty.encode(quote!(#field[i]), &elem_width);

                        quote!({
                            let mut result = 0;
                            for i in 0..#len {
                                result <<= #elem_width;
                                result |= #elem_encoded;
                            }

                            result
                        })
                    }
                }
            }
        }

        impl PrimeType {
            fn decode(&self, field_as_repr: TokenStream2, field_width: &Width) -> TokenStream2 {
                let inner = quote!(#field_as_repr & (!0 >> (ITEM_REPR_WIDTH - (#field_width))));

                match self {
                    Self::Bool => quote! { (#inner) == 1 },
                    Self::UInt(_) => quote! { (#inner) as _ },
                    Self::Other(_) => {
                        quote!(unsafe { ::regent::Bitwise::from_repr_unchecked(#inner) })
                    }
                }
            }

            fn encode(&self, repr_width: &Width, value: syn::Expr) -> TokenStream2 {
                let expr = match self {
                    Self::Other(_) => quote! { ::regent::Bitwise::to_repr(#field) },
                    _ => quote! { (#field as ItemRepr) },
                };

                quote! { #expr & (!0 >> (ITEM_REPR_WIDTH - (#field_width))) }
            }
        }

        let syn::Field {
            attrs: field_attrs, ident: field_ident, ty: field_ty, vis: field_vis, ..
        } = field;

        let (field_getter_ident, field_setter_ident) = match field_ident {
            Some(it) => (it.clone(), format_ident!("set_{it}")),
            None => (
                format_ident!("_{i}", span = item_span),
                format_ident!("set_{i}", span = item_span),
            ),
        };
        let field_ident = &field_getter_ident;
        let field_span = field_getter_ident.span();

        let field_ty = unwrap!(Type::parse(field_span, field_ty));
        unwrap!(field_ty.validate(field_span));

        // This is the position of the least-significant bit of this field.
        let field_offset = item_width.clone();
        // This is the exact width of this field.
        let field_width = field_ty.width();
        item_width += &field_width;

        // This is a type used to represent this field in arguments and return types.
        let field_ty = field_ty.as_rust_primitives();
        if !field_ty.exists() {
            fail!(
                field_span,
                "'bitwise' field cannot be represented in terms of primitive Rust types"
            );
        }

        let mut field_value = None;
        for attr in field_attrs {
            // FIXME: don't unwrap.
            let metas = darling::util::parse_attribute_to_meta_list(&attr).unwrap();
            if metas.path.is_ident("constant") {
                #[derive(darling::FromMeta)]
                struct ConstantArgs {
                    value: Option<syn::Expr>,
                }

                let nested_metas: Vec<_> = metas.nested.into_iter().collect();
                // FIXME: don't unwrap.
                let args = ConstantArgs::from_list(&nested_metas).unwrap();
                field_value = Some(match args.value {
                    Some(it) => it.into_token_stream(),
                    None => quote!(<#field_ty as ::core::default::Default>::default()),
                });
            } else {
                fail!(field_span, "invalid attribute")
            }
        }

        let new_glue: TokenStream2;
        if let Some(field_value) = field_value {
            // This is the simple case for constant fields only. We don't need to generate getters
            // or setters.

            let field_decoded = field_ty.decode(quote!(repr), &field_width);
            from_repr_checked_body.extend(quote!({
                let repr: ItemRepr = repr >> (#field_offset);
                let actual_value: #field_ty = #field_decoded;
                let expected_value: #field_ty = #field_value;
                if actual_value != expected_value {
                    return None;
                }
            }));
            new_glue = field_ty.encode(field_value, &field_width);
        } else {
            // This is the more complicated case for non-constant fields.

            let field_decoded = field_ty.decode(quote!(field_as_repr), &field_width);
            let field_encoded = field_ty.encode(quote!(field), &field_width);
            new_glue = field_ty.encode(field_ident.to_token_stream(), &field_width);

            item_methods.push(Method {
                sig: quote!(#field_vis fn #field_getter_ident(&self) -> #field_ty),
                body: quote! {
                    let mut field_as_repr: ItemRepr = self.0 >> (#field_offset);

                    #field_decoded
                },
            });
            item_methods.push(Method {
                sig: quote!(#field_vis fn #field_setter_ident(&mut self, field: #field_ty)),
                body: quote! {
                    let mut field_as_repr: ItemRepr = #field_encoded;
                    self.0 &= !((!0 >> (ITEM_REPR_WIDTH - (#field_width))) << (#field_offset));
                    self.0 |= field_as_repr << (#field_offset);
                },
            });
            item_new_args.push(quote!(#field_ident: #field_ty));
        }
        new_stmts.push(quote! {
            bits <<= #field_width;
            bits |= #new_glue;
        });
    }

    let mut prelude = TokenStream2::new();
    assert_expected_width_is_correct!(expected_width, item_span, item_width, prelude);
    let item_repr =
        unwrap!(determine_item_repr(expected_width, item_span, &mut item_attrs, &item_width));

    new_stmts.reverse();
    item_methods.push(Method {
        sig: quote!(#item_vis fn new(#(#item_new_args),*) -> Self),
        body: quote! {
            let mut bits: ItemRepr = 0;
            #(#new_stmts)*

            Self(bits)
        },
    });

    let mut output = Item {
        attrs: quote! {
            #(#item_attrs)*
            #[repr(transparent)]
        },
        vis: item_vis,
        token: quote!(struct),
        ident: item_ident,
        body: quote! { (#item_repr); },
        methods: item_methods,
        bitwise_impl: BitwiseImpl {
            width: item_width,
            repr: item_repr,
            from_repr_unchecked: quote!(Self(repr)),
            from_repr_checked: quote! {
                #from_repr_checked_body

                Some(Self(repr))
            },
            to_repr: quote!(self.0),
        },
    }
    .into_token_stream();
    output.extend(prelude);

    output.into()
}

///// PRIVATE API //////////////////////////////////////////////////////////////////////////////////

/// Returns an error generated by [`make_error`] if `generics` is non-empty.
///
/// [`bitwise`] does not support generic items. This function helps ensure that the current item is
/// not generic.
fn check_generics(generics: syn::Generics) -> Result<(), TokenStream> {
    let syn::Generics { params, where_clause, .. } = generics;
    if !params.is_empty() {
        return Err(make_error(
            params.span(),
            "generics parameters are not supported in this context",
        ));
    }
    if let Some(clause) = where_clause {
        return Err(make_error(clause.span(), "'where clauses' are not supported in this context"));
    }

    Ok(())
}

enum EnforceItemWidthStrategy {
    /// The expected width is correct, and nothing need be done.
    None,
    /// The expected width is incorrect, and this error should be returned during macro evaluation.
    Fail(TokenStream),
    /// The correctness of the expected width is indeterminate at macro evaluation time, so this
    /// expression should be inserted in a const context to perform the check at compile-time.
    ConstCheck(syn::Expr),
}

impl EnforceItemWidthStrategy {
    /// Devises a strategy to enforce the expected bit-width of an item.
    ///
    /// [`bitwise`] accepts `size` and `width` attribute arguments which are intended to make
    /// compile-time guarantees about the `Bitwise::WIDTH` of the generated item. In the simple
    /// case, the width can be calculated exactly during macro evaluation and an error is
    /// returned if it differs from `expected_width`. Otherwise, if the item is a struct
    /// containing custom types that implement `Bitwise`, the exact width is indeterminate at
    /// macro evaluation time and so enforcement of `expected_width` is deferred to compile-time
    /// via an assertion in a const context.
    fn devise(expected_width: usize, actual_width: &Width) -> Self {
        match actual_width {
            Width::Lit { span, value: actual_width } => {
                if expected_width != *actual_width {
                    return Self::Fail(make_error(
                        *span,
                        format!("item width is {actual_width} bits, should be {expected_width}"),
                    ));
                }
            }
            Width::Expr(_) => {
                // We don't have enough information to evaluate `actual_width` at macro
                // evaluation time, but we can generate Rust code to do so at compile-time.
                return Self::const_check(expected_width, actual_width);
            }
        }

        Self::None
    }

    fn const_check(expected_width: usize, actual_width: &Width) -> Self {
        let actual_width = actual_width.into_grouped_expr();
        // FIXME: print item ident so the user knows that the heck we're talking about
        let panic_msg = format!("item width should be {expected_width}");
        let span = Span2::call_site();

        // This looks like:
        //   if expected_width != actual_width {
        //       ::core::panicking::panic(#panic_msg);
        //   }
        Self::ConstCheck(
            syn::ExprIf {
                attrs: Vec::new(),
                if_token: syn::Token![if](span),
                cond: Box::new(
                    syn::ExprBinary {
                        attrs: Vec::new(),
                        left: Box::new(
                            syn::ExprLit {
                                attrs: Vec::new(),
                                lit: syn::LitInt::new(&expected_width.to_string(), span).into(),
                            }
                            .into(),
                        ),
                        op: syn::BinOp::Ne(syn::Token![!=](span)),
                        right: Box::new(actual_width.into()),
                    }
                    .into(),
                ),
                then_branch: syn::Block {
                    brace_token: Default::default(),
                    stmts: vec![syn::Stmt::Expr(
                        syn::ExprCall {
                            attrs: Vec::new(),
                            func: Box::new(
                                syn::ExprPath {
                                    attrs: Vec::new(),
                                    qself: None,
                                    path: syn::Path {
                                        leading_colon: Some(Default::default()),
                                        segments: Punctuated::from_iter(
                                            ["core", "panicking", "panic"].map(|it| {
                                                syn::PathSegment {
                                                    ident: syn::Ident::new(it, span),
                                                    arguments: syn::PathArguments::None,
                                                }
                                            }),
                                        ),
                                    },
                                }
                                .into(),
                            ),
                            paren_token: Default::default(),
                            args: Punctuated::from_iter::<[syn::Expr; 1]>([syn::ExprLit {
                                attrs: Vec::new(),
                                lit: syn::LitStr::new(&panic_msg, span).into(),
                            }
                            .into()]),
                        }
                        .into(),
                        Some(syn::Token![;](span)),
                    )],
                },
                else_branch: None,
            }
            .into(),
        )
    }
}

/// Returns the best representation for an item.
///
/// If `item_attrs` contains a `#[repr(...)]` attribute, the attribute argument is parsed as a
/// [`UIntType`] and is returned. The attribute itself is then removed from `item_attrs` so it will
/// not appear in the generated item.
///
/// Otherwise, `expected_width` and `item_width` are consulted, in that order, to generate
/// `UIntType`s of those widths. This function ultimately fails if `item_width` is a compile-time
/// expression (indeterminate at macro evaluation time) and all previous strategies have been
/// exhausted, in which case a [`TokenStream`] generated by [`make_error`] is returned.
fn determine_item_repr(
    expected_width: Option<usize>,
    item_span: Span2,
    item_attrs: &mut Vec<syn::Attribute>,
    item_width: &Width,
) -> Result<UIntType, TokenStream> {
    if let Some((i, attr)) =
        item_attrs.iter().enumerate().find(|(_, attr)| attr.path().is_ident("repr"))
    {
        let (arg, arg_span) = match attr.parse_args::<syn::Ident>() {
            Ok(it) => (it.to_string(), it.span()),
            Err(e) => {
                return Err(e.into_compile_error().into());
            }
        };
        let repr = match UIntType::parse(arg_span, &arg) {
            Some(Ok(ty)) if ty.exists() => ty,
            Some(Err(e)) => {
                return Err(e);
            }
            _ => {
                return Err(make_error(arg_span, "this must be an unsigned integer primitive"));
            }
        };
        // It shouldn't really matter when we do this; we just need to do it at some point.
        item_attrs.remove(i);

        Ok(repr)
    } else {
        let repr = if let Some(width) = expected_width {
            UIntType { width }
        } else {
            match item_width {
                Width::Lit(width) => UIntType { width: *width },
                Width::Expr(_) => {
                    return Err(make_error(
                        item_span,
                        "not enough information to compute item width at macro evaluation time",
                    ));
                }
            }
        }
        .round_up();
        if !repr.exists() {
            return Err(make_error(
                item_span,
                "this item cannot be represented by any existing integer primitive",
            ));
        }

        Ok(repr)
    }
}

/// An item generated by [`bitwise`].
struct Item {
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    /// The token identifying what kind of item this is (e.g., `enum`, `struct`).
    kind: TokenStream2,
    ident: syn::Ident,
    body: TokenStream2,
    methods: Vec<Method>,
    bitwise_impl: BitwiseImpl,
}

impl ToTokens for Item {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let Self { attrs, vis, kind, ident, body, .. } = self;
        let method_prelude = quote! {
            #[allow(unused)]
            const ITEM_WIDTH: usize = <#ident as ::regent::Bitwise>::WIDTH;
            #[allow(unused)]
            const ITEM_REPR_WIDTH: usize = <#ident as ::regent::BitwiseExt>::REPR_WIDTH;
            #[allow(unsued)]
            type ItemRepr = <#ident as ::regent::Bitwise>::Repr;
        };
        let methods: TokenStream2 = self
            .methods
            .iter()
            .map(|it| {
                let Method { sig, body } = it;

                quote! {
                    #sig {
                        #method_prelude
                        #body
                    }
                }
            })
            .collect();
        let bitwise_width = &self.bitwise_impl.width.into_expr();
        let bitwise_repr = &self.bitwise_impl.repr;
        let bitwise_from_repr_unchecked = &self.bitwise_impl.from_repr_unchecked;
        let bitwise_from_repr_checked = &self.bitwise_impl.from_repr_checked;
        let bitwise_to_repr = &self.bitwise_impl.to_repr;

        let impl_ =
            if methods.is_empty() { TokenStream2::new() } else { quote!(impl #ident { #methods }) };

        let impl_trait_token =
            if cfg!(feature = "nightly") { quote!(impl const) } else { quote!(impl) };

        tokens.extend(quote! {
            #(#attrs)*
            #vis #kind #ident #body

            #impl_

            #impl_trait_token ::regent::Bitwise for #ident {
                const WIDTH: usize = #bitwise_width;

                type Repr = #bitwise_repr;

                #[inline]
                unsafe fn from_repr_unchecked(repr: Self::Repr) -> Self {
                    #method_prelude
                    #bitwise_from_repr_unchecked
                }

                fn from_repr_checked(repr: Self::Repr) -> Option<Self> {
                    #method_prelude
                    #bitwise_from_repr_checked
                }

                #[inline]
                fn to_repr(&self) -> Self::Repr {
                    #method_prelude
                    #bitwise_to_repr
                }
            }
        })
    }
}

struct Method {
    sig: TokenStream2,
    body: TokenStream2,
}

struct BitwiseImpl {
    width: Width,
    repr: UIntType,
    from_repr_unchecked: TokenStream2,
    from_repr_checked: TokenStream2,
    to_repr: TokenStream2,
}

/// The bit-width of a type known to [`bitwise`].
type Width = ConstUsizeExpr;

/// A const expression that evaluates to a `usize` at compile-time.
#[derive(Clone)]
enum ConstUsizeExpr {
    /// A `usize` literal whose value is known at macro evaluation time.
    Lit { span: Span2, value: usize },
    /// A `usize` expression whose value is known only at compile-time.
    Expr(syn::Expr),
}

impl ConstUsizeExpr {
    /// A const expression represented by the literal `0usize`.
    fn zero(span: Span2) -> Self {
        Self::Lit { span, value: 0 }
    }

    fn span(&self) -> Span2 {
        match self {
            Self::Lit { span, .. } => *span,
            Self::Expr(inner) => inner.span(),
        }
    }

    /// Converts this into a [`syn::ExprGroup`].
    fn into_grouped_expr(self) -> syn::ExprGroup {
        let span = self.span();
        let expr = match self {
            Self::Lit { value, .. } => syn::ExprLit {
                attrs: Vec::new(),
                lit: syn::LitInt::new(&value.to_string(), span).into(),
            }
            .into(),
            Self::Expr(inner) => inner,
        };

        syn::ExprGroup {
            attrs: Vec::new(),
            group_token: syn::token::Group { span },
            expr: Box::new(expr),
        }
    }

    /// Creates a [`syn::ExprGroup`] that masks the least-significant bits of an expression.
    fn into_mask(self, repr_width: Self) -> syn::ExprGroup {
        let span = self.span();

        // This looks like:
        //   !0 >> (#repr_width - #self)
        syn::ExprGroup {
            attrs: Vec::new(),
            group_token: syn::token::Group { span },
            expr: Box::new(
                syn::ExprBinary {
                    attrs: Vec::new(),
                    left: Box::new(
                        syn::ExprUnary {
                            attrs: Vec::new(),
                            op: syn::UnOp::Not(syn::Token![!](span)),
                            expr: Box::new(
                                syn::ExprLit {
                                    attrs: Vec::new(),
                                    lit: syn::LitInt::new("0", span).into(),
                                }
                                .into(),
                            ),
                        }
                        .into(),
                    ),
                    op: syn::BinOp::Shr(syn::Token![>>](span)),
                    right: Box::new(
                        syn::ExprBinary {
                            attrs: Vec::new(),
                            left: Box::new(repr_width.into_grouped_expr().into()),
                            op: syn::BinOp::Sub(syn::Token![-](span)),
                            right: Box::new(self.into_grouped_expr().into()),
                        }
                        .into(),
                    ),
                }
                .into(),
            ),
        }
    }

    /// Applies a binary operation to two [`syn::ExprGroup`]s and returns the result.
    fn apply_binop(lhs: syn::ExprGroup, op: syn::BinOp, rhs: syn::ExprGroup) -> Self {
        Self::Expr(
            syn::ExprBinary {
                attrs: Vec::new(),
                left: Box::new(lhs.into()),
                op,
                right: Box::new(rhs.into()),
            }
            .into(),
        )
    }
}

/// Implements `BinOp` and `BinOpAssign` -like traits for [`ConstUsizeExpr`].
macro_rules! impl_binop_for_const_usize_expr {
    (
        $op:tt {
            $trait:tt, $fn:tt $(,)?
        },
        $op_assign:tt {
            $trait_assign:tt, $fn_assign:tt $(,)?
        } $(,)?
    ) => {
        impl std::ops::$trait for ConstUsizeExpr {
            type Output = Self;

            fn $fn(self, rhs: Self) -> Self::Output {
                match (self, rhs) {
                    (Self::Lit { span: lspan, value: lhs }, Self::Lit { span: rspan, value: rhs }) => {
                        Self::Lit {
                            span: Span2::,
                            value: lhs $op rhs,
                        }
                    }
                    (Self::Expr(spanned), _) | (_, Self::Expr(spanned)) => {
                        let span = spanned.span();

                        Self::apply_binop(self.into_grouped_expr(span), binop!(span, $op, $trait), rhs.into_grouped_expr(span))
                    }
                }
            }
        }

        impl std::ops::$trait_assign<Self> for ConstUsizeExpr {
            fn $fn_assign(&mut self, rhs: Self) {
                if let (Self::Lit(inner), Self::Lit(rhs)) = (self, rhs) {
                    *inner $op_assign rhs;
                } else {
                    // FIXME: fix span
                    let span = Span2::mixed_site();

                    *self = Self::apply_binop(span, Cow::Borrowed(self), Cow::Owned(rhs), binop!(span, $op_assign, $trait_assign));
                }
            }
        }

        impl std::ops::$trait_assign<&Self> for ConstUsizeExpr {
            fn $fn_assign(&mut self, rhs: &Self) {
                if let (Self::Lit(inner), Self::Lit(rhs)) = (self, rhs) {
                    *inner $op_assign *rhs;
                } else {
                    // FIXME: fix span
                    let span = Span2::mixed_site();

                    *self = Self::apply_binop(span, Cow::Borrowed(self), Cow::Borrowed(rhs), binop!(span, $op_assign, $trait_assign));
                }
            }
        }
    };
}

impl_binop_for_const_usize_expr!(
    * { Mul, mul },
    *= { MulAssign, mul_assign },
);
impl_binop_for_const_usize_expr!(
    + { Add, add },
    += { AddAssign, add_assign },
);

impl std::iter::Sum for ConstUsizeExpr {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut acc = Self::zero();
        for elem in iter {
            acc += &elem;
        }

        acc
    }
}

/// The type of an enum variant or struct field.
#[derive(Clone)]
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
    fn parse(span: Span2, ty: syn::Type) -> Result<Self, TokenStream> {
        match ty {
            syn::Type::Path(ty) => PrimeType::parse(span, ty).map(Self::Prime),
            syn::Type::Tuple(syn::TypeTuple { elems: tys, .. }) => {
                let tys = tys
                    .into_iter()
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
                let syn::Type::Path(ty) = *ty else {
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
            _ => Err(make_error(span, "unsupported type")),
        }
    }

    fn as_rust_primitives(self) -> Self {
        match self {
            Self::Prime(ty) => Self::Prime(ty.as_rust_primitive()),
            Self::Tuple(tys) => {
                Self::Tuple(tys.into_iter().map(|it| it.as_rust_primitive()).collect())
            }
            Self::Array { ty, len } => Self::Array { ty: ty.as_rust_primitive(), len },
        }
    }

    fn exists(&self) -> bool {
        match self {
            Self::Prime(ty) => ty.exists(),
            Self::Tuple(tys) => tys.iter().all(PrimeType::exists),
            Self::Array { ty, .. } => ty.exists(),
        }
    }

    fn width(&self) -> Width {
        match self {
            Self::Prime(ty) => ty.width(),
            Self::Tuple(tys) => tys.iter().map(PrimeType::width).sum(),
            Self::Array { ty, len } => ty.width() * Width::Lit(*len),
        }
    }

    fn validate(&self, span: Span2) -> Result<(), TokenStream> {
        match self {
            Type::Tuple(tys) => {
                if tys.is_empty() {
                    return Err(make_error(span, "'bitwise' fields cannot be the unit type"));
                }
            }
            Type::Array { len, .. } => {
                if *len == 0 {
                    return Err(make_error(span, "'bitwise' fields cannot be zero-sized arrays"));
                }
            }
            _ => {}
        }

        Ok(())
    }
}

impl ToTokens for Type {
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

#[derive(Clone)]
enum PrimeType {
    Bool,
    UInt(UIntType),
    Other(syn::TypePath),
}

impl PrimeType {
    fn parse(span: Span2, ty: syn::TypePath) -> Result<Self, TokenStream> {
        if let Some(ty) = ty.path.get_ident().map(ToString::to_string) {
            if ty == "bool" {
                return Ok(Self::Bool);
            } else if let Some(result) = UIntType::parse(span, &ty) {
                return result.map(Self::UInt);
            }
        }

        Ok(Self::Other(ty))
    }

    fn as_rust_primitive(self) -> Self {
        if let Self::UInt(ty) = self {
            Self::UInt(ty.round_up())
        } else {
            self
        }
    }

    fn exists(&self) -> bool {
        match self {
            Self::UInt(ty) => ty.exists(),
            _ => true,
        }
    }

    fn width(&self) -> Width {
        match self {
            Self::Bool => Width::Lit(1),
            Self::UInt(ty) => Width::Lit(ty.width),
            Self::Other(ty) => Width::Expr(quote!(<#ty as ::regent::Bitwise>::WIDTH)),
        }
    }
}

impl ToTokens for PrimeType {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            Self::Bool => {
                tokens.extend(quote!(bool));
            }
            Self::UInt(ty) => {
                ty.to_tokens(tokens);
            }
            Self::Other(ty) => {
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
    fn parse(span: Span2, ty: &str) -> Option<Result<Self, TokenStream>> {
        let Some(("", width)) = ty.split_once('u') else {
            return None;
        };
        let Ok(width) = width.parse() else {
            return Some(Err(make_error(span, "failed to parse integer width suffix")));
        };
        if width == 0 {
            return Some(Err(make_error(span, "'bitwise' does not support zero-sized types")));
        }

        Some(Ok(Self { width }))
    }

    fn round_up(self) -> Self {
        let width = if self.width <= 8 {
            8
        } else {
            // This is the 'magnitude' of `width`, or the integer component of `log2(width)`.
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

impl ToTokens for UIntType {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        tokens.extend(format_ident!("u{}", self.width).into_token_stream());
    }
}
