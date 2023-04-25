// SPDX-License-Identifier: MPL-2.0

//! Procedural macros for [Regent].
//!
//! [Regent]: https://crates.io/crates/regent

///// PROGRAMMER'S NOTE ////////////////////////////////////////////////////////////////////////////
//
// Throughout *regent-internals*, we will distinguish between 'macro evaluation time' (when the
// entrypoint to a proc macro is invoked) and 'compile-time' (when the crate invoking a proc macro
// is fully-expanded) to explain the kinds of information available to [`bitwise`] and which must be
// supplied via other means, e.g., in attribute arguments.

use std::borrow::Cow;

use proc_macro::TokenStream;
use proc_macro2::{Span as Span2, TokenStream as TokenStream2};
use syn::spanned::Spanned as _;

///// UTILITY MACROS ///////////////////////////////////////////////////////////////////////////////

/// Like [`try`](std::try) except the return type of the containing function is `T` instead of
/// [`Result<T, E>`](std::result::Result).
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

/// Creates an [`Error`] with the given message and, optionally, span.
///
/// If no span is specified, [`Span2::call_site`] is used.
macro_rules! err {
    ($fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        err!(proc_macro2::Span::call_site();  $fmt $(, $fmt_arg)*)
    };
    ($span:expr ; $fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        $crate::Error(syn::Error::new($span, format!($fmt $(, $fmt_arg)*)))
    };
}

/// The error type returned by fallible internal functions.
///
/// This is a wrapper over [`syn::Error`] and exists only to provide convenience implementations of
/// [`Into`] for `syn::Error` and [`TokenStream`].
struct Error(syn::Error);

impl From<Error> for syn::Error {
    fn from(e: Error) -> Self {
        e.0
    }
}

impl From<Error> for TokenStream {
    fn from(e: Error) -> Self {
        e.0.into_compile_error().into()
    }
}

///// PUBLIC API ///////////////////////////////////////////////////////////////////////////////////

mod on_enum;
mod on_struct;

/// Does the thing.
///
/// See the [README] for usage information.
///
/// [README]: https://github.com/norepimorphism/regent/blob/main/README.md
#[proc_macro_attribute]
pub fn bitwise(args: TokenStream, item: TokenStream) -> TokenStream {
    let args = Args::parse(args)?;
    let expected_width = args.expected_width();

    match syn::parse_macro_input!(item as _) {
        syn::Item::Enum(item) => on_enum::bitwise(expected_width, item),
        syn::Item::Struct(item) => on_struct::bitwise(expected_width, item),
        item => err!(item.span(); "this kind of item is not supported").into(),
    }
}

/// Recognized arguments to the `bitwise` attribute.
#[derive(Default)]
struct Args {
    /// The 'size' argument, if any.
    ///
    /// This determines the size, in bytes, of the emitted item. This argument is
    /// mutually-exclusive with the 'width' argument.
    size: Option<usize>,
    /// The 'width' argument, if any.
    ///
    /// This determines the width, in bits, of the emitted item. This argument is
    /// mutually-exclusive with the 'size' argument.
    width: Option<usize>,
}

impl Args {
    /// Parses comma-separated attribute arguments from the given [`TokenStream`].
    fn parse(args: TokenStream) -> Result<Self, TokenStream> {
        let mut result = Self::default();
        let error = result.parse_impl(args);
        if !error.is_empty() {
            return Err(error);
        }
        if result.size.is_some() && result.width.is_some() {
            return err!("`size` and `width` attribute arguments are mutually exclusive").into();
        }

        Ok(result)
    }

    /// Parses comma-separated attribute arguments from the given [`TokenStream`].
    ///
    /// This is an implementation detail of [`parse`](Self::parse).
    fn parse_impl(&mut self, args: TokenStream) -> TokenStream {
        let parser = syn::meta::parser(|meta| {
            let ident = meta.path.get_ident().ok_or_else(|| -> syn::Error {
                err!(meta.path.span(); "attribute argument should be an identifier").into()
            })?;
            let arg = if ident == "size" {
                &mut self.size
            } else if ident == "width" {
                &mut self.width
            } else {
                return Err(err!(ident.span(); "attribute argument is not supported").into());
            };
            if arg.is_some() {
                // TODO: warn against duplicate arguments
            }
            let value = meta.value().and_then(|it| it.parse::<syn::LitInt>()).and_then(|it| it.base10_parse())?;
            *arg = Some(value);

            Ok(())
        });
        syn::parse_macro_input!(args with parser);

        Default::default()
    }

    fn expected_width(&self) -> Option<usize> {
        self.width.or_else(|| self.size.map(|it| it * 8))
    }
}

///// PRIVATE API //////////////////////////////////////////////////////////////////////////////////

/// Returns an [`Error`] if `generics` is non-empty.
///
/// [`bitwise`] does not support generic items. This function helps ensure that the current item is
/// not generic.
///
/// `generics` is passed by-value to discourage its usage after this function is called.
fn check_generics(generics: syn::Generics) -> Result<(), Error> {
    let syn::Generics { params, where_clause, .. } = generics;
    if !params.is_empty() {
        return Err(err!(params.span(); "generics parameters are not supported in this context"));
    }
    if let Some(clause) = where_clause {
        return Err(err!(clause.span(); "'where clauses' are not supported in this context"));
    }

    Ok(())
}

/// A strategy to enforce the expected bit-width of an item.
enum EnforceItemWidthStrategy {
    /// The expected width is correct, and nothing needs to be done.
    None,
    /// The expected width is incorrect, and this error should be returned during macro evaluation.
    Fail(Error),
    /// The correctness of the expected width is indeterminate at macro evaluation time, so this
    /// expression should be inserted in a const context to perform the check at compile-time.
    ConstCheck(syn::Expr),
}

impl EnforceItemWidthStrategy {
    /// Devises an `EnforceItemWidthStrategy`.
    ///
    /// [`bitwise`] accepts `size` and `width` attribute arguments which are intended to make
    /// compile-time guarantees about the `Bitwise::WIDTH` of the emitted item. In the simple case,
    /// the width is calculated exactly during macro evaluation and an error is returned if it
    /// differs from `expected_width`. Otherwise, if the item is a struct containing custom
    /// implementors of`Bitwise`, the exact width is indeterminate at macro evaluation time and so
    /// enforcement of `expected_width` is deferred to compile-time via an assertion in a const
    /// context.
    fn devise(expected_width: usize, actual_width: &Width) -> Self {
        match actual_width {
            Width::Lit { span, value: actual_width } => {
                if expected_width != *actual_width {
                    return Self::Fail(err!(
                        *span;
                        "item width is {actual_width} bits, should be {expected_width}",
                    ));
                }
            }
            Width::Expr(_) => {
                // We don't have enough information to evaluate `actual_width` at macro evaluation
                // time, but we can emit Rust code to do so at compile-time.
                return Self::const_check(expected_width, actual_width);
            }
        }

        Self::None
    }

    fn const_check(expected_width: usize, actual_width: &Width) -> Self {
        let span = actual_width.span();

        // FIXME: print item ident so the user knows that the heck we're talking about
        let panic_msg = format!("item width should be {expected_width}");

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
                        right: Box::new(actual_width.into_grouped_expr().into()),
                    }
                    .into(),
                ),
                then_branch: syn::Block {
                    brace_token: syn::token::Brace(span),
                    stmts: vec![syn::Stmt::Expr(
                        syn::ExprCall {
                            attrs: Vec::new(),
                            func: Box::new(
                                syn::ExprPath {
                                    attrs: Vec::new(),
                                    qself: None,
                                    path: syn::Path {
                                        leading_colon: Some(syn::Token![::](span)),
                                        segments: ["core", "panicking", "panic"]
                                            .map(|it| syn::PathSegment {
                                                ident: syn::Ident::new(it, span),
                                                arguments: syn::PathArguments::None,
                                            })
                                            .into_iter()
                                            .collect(),
                                    },
                                }
                                .into(),
                            ),
                            paren_token: syn::token::Paren(span),
                            args: [syn::Expr::Lit(syn::ExprLit {
                                attrs: Vec::new(),
                                lit: syn::LitStr::new(&panic_msg, span).into(),
                            })]
                            .into_iter()
                            .collect(),
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
/// exhausted, in which case an [`Error`] is returned.
fn determine_item_repr(
    expected_width: Option<usize>,
    item_span: Span2,
    item_attrs: &mut Vec<syn::Attribute>,
    item_width: &Width,
) -> Result<UIntType, Error> {
    if let Some((i, attr)) =
        item_attrs.iter().enumerate().find(|(_, attr)| attr.path().is_ident("repr"))
    {
        let (arg, arg_span) = match attr.parse_args::<syn::Ident>() {
            Ok(it) => (it.to_string(), it.span()),
            Err(e) => {
                return Err(Error(e));
            }
        };
        let repr = match UIntType::parse(arg_span, &arg) {
            Some(Ok(ty)) if ty.exists() => ty,
            Some(Err(e)) => {
                return Err(e);
            }
            _ => {
                return Err(err!(arg_span; "this must be an unsigned integer primitive"));
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
                    return Err(err!(
                        item_span;
                        "not enough information to compute item width at macro evaluation time",
                    ));
                }
            }
        }
        .round_up();
        if !repr.exists() {
            return Err(err!(
                item_span;
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
            group_token: syn::token::Group(span),
            expr: Box::new(expr),
        }
    }

    /// Creates a [`syn::ExprGroup`] that masks the least-significant bits of an expression.
    fn into_mask(self, repr_width: Self) -> syn::ExprGroup {
        let span = self.span();

        // !0 >> (#repr_width - #self)
        syn::ExprGroup {
            attrs: Vec::new(),
            group_token: syn::token::Group(span),
            expr: Box::new(
                syn::ExprBinary {
                    attrs: Vec::new(),
                    // !0
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
                    // >>
                    op: syn::BinOp::Shr(syn::Token![>>](span)),
                    // #repr_width - #self
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

#[derive(Clone, Copy)]
struct UIntType {
    width: usize,
}

impl UIntType {
    fn parse(span: Span2, ty: &str) -> Option<Result<Self, Error>> {
        let Some(("", width)) = ty.split_once('u') else {
            // This is not even an unsigned integer.
            return None;
        };
        let Ok(width) = width.parse() else {
            return Some(Err(err!(span; "failed to parse integer width suffix")));
        };
        if width == 0 {
            return Some(Err(err!(span; "'bitwise' does not support zero-sized types")));
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

impl From<UIntType> for syn::TypePath {
    fn from(ty: UIntType) -> Self {
        Self {
            qself: None,
            path: [format!("u{}", ty.width)].into_iter().collect(),
        }
    }
}
