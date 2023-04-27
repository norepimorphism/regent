// SPDX-License-Identifier: MPL-2.0

//! Procedural macros for [Regent].
//!
//! [Regent]: https://crates.io/crates/regent

use proc_macro::TokenStream;
use proc_macro2::{Span as Span2, TokenStream as TokenStream2};
use syn::{__private::ToTokens, spanned::Spanned as _};

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
/// If no span is specified, [`call_site`](Span2::call_site) is used.
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

    let result = match syn::parse_macro_input!(item as _) {
        syn::Item::Enum(item) => on_enum::bitwise(expected_width, item),
        syn::Item::Struct(item) => on_struct::bitwise(expected_width, item),
        item => Err(err!(item.span(); "item must be a struct or enum").into()),
    };

    match result {
        Ok(it) => it.into_token_stream().into(),
        Err(e) => e.into(),
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
    fn parse(args: TokenStream) -> Result<Self, Error> {
        let mut result = Self::default();
        syn::meta::parser(|meta| {
            let ident = meta.path.get_ident().ok_or_else(|| -> syn::Error {
                err!(meta.path.span(); "attribute argument must be an identifier").into()
            })?;
            let span = ident.span();
            let arg = match ident {
                "size" => &mut result.size,
                "width" => &mut result.width,
                _ => {
                    return Err(err!(span; "attribute argument is not supported").into());
                }
            };
            if arg.is_some() {
                return Err(err!(span; "attribute argument is a duplicate").into());
            }
            let value = meta.value().and_then(|it| it.parse::<syn::LitInt>()).and_then(|it| it.base10_parse())?;
            *arg = Some(value);

            Ok(())
        })
        .parse(args)
        .map_err(Error)?;

        if result.size.is_some() && result.width.is_some() {
            return err!("`size` and `width` attribute arguments are mutually exclusive").into();
        }

        Ok(result)
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

/// The bit-width of a type.
type Width = crate::ConstUsizeExpr;

/// A const expression that evaluates to a `usize` at compile-time.
#[derive(Clone)]
enum ConstUsizeExpr {
    /// A `usize` literal whose value is known at macro evaluation time (MET).
    Met { span: Span2, value: usize },
    /// A `usize` expression whose value is known only at compile-time (CT).
    Ct(syn::Expr),
}

impl ConstUsizeExpr {
    /// A const expression represented by the literal `0usize`.
    fn zero(span: Span2) -> Self {
        Self::Met { span, value: 0 }
    }

    /// The source code span of this expression.
    fn span(&self) -> Span2 {
        match self {
            Self::Met { span, .. } => *span,
            Self::Ct(inner) => inner.span(),
        }
    }

    /// Converts this into a [`syn::Expr`].
    fn into_expr(self) -> syn::Expr {
        let span = self.span();
        let expr = match self {
            Self::Met { value, .. } => syn::ExprLit {
                attrs: Vec::new(),
                lit: syn::LitInt::new(&value.to_string(), span).into(),
            }
            .into(),
            Self::Ct(inner) => inner,
        };

        syn::ExprParen {
            attrs: Vec::new(),
            paren_token: syn::token::Paren(span),
            expr: Box::new(expr),
        }
        .into()
    }

    /// Creates a [`syn::Expr`] that masks the least-significant bits of an expression.
    ///
    /// The expression is of the form:
    ///
    /// ```no_run
    /// (!0 >> (#repr_width - #self))
    /// ```
    fn into_mask(self, repr_width: Self) -> syn::Expr {
        let span = self.span();

        let zero_lit = syn::ExprLit {
            attrs: Vec::new(),
            lit: syn::LitInt::new("0", span).into(),
        }
        .into();
        let lhs_expr = syn::ExprUnary {
            attrs: Vec::new(),
            op: syn::UnOp::Not(syn::Token![!](span)),
            expr: Box::new(zero_lit),
        }
        .into();

        let rhs_expr = syn::ExprBinary {
            attrs: Vec::new(),
            left: Box::new(repr_width.into_expr()),
            op: syn::BinOp::Sub(syn::Token![-](span)),
            right: Box::new(self.into_expr()),
        }
        .into();

        syn::ExprParen {
            attrs: Vec::new(),
            paren_token: syn::token::Paren(span),
            expr: Box::new(
                syn::ExprBinary {
                    attrs: Vec::new(),
                    left: Box::new(lhs_expr),
                    op: syn::BinOp::Shr(syn::Token![>>](span)),
                    right: Box::new(rhs_expr),
                }
                .into(),
            ),
        }
        .into()
    }

    /// Adds the given integral value to this expression.
    fn add(&mut self, rhs: &Self) {
        match (self, rhs) {
            (Self::Met { value: lhs, .. }, Self::Met { value: rhs, .. }) => {
                *lhs += rhs;
            }
            (Self::Met { span, value }, Self::Ct(rhs)) => {
                *self = Self::Ct(syn::ExprBinary {
                    attrs: Vec::new(),
                    left: Box::new(self.into_expr()),
                    op: syn::BinOp::Add(syn::Token![+](*span)),
                    right: Box::new(rhs.clone()),
                }.into());
            }
        }
    }
}

/// An unsigned integer type.
#[derive(Clone, Copy)]
struct UIntType {
    /// The bit-width of this type.
    width: usize,
}

impl UIntType {
    /// Attempts to parse a `UIntType` from the given string.
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

    /// Determines if this type represents an unsigned integer primitive that exists in Rust today.
    ///
    /// This returns `true` if [`width`](Self::width) is a power of 2 between 8 and 128, inclusive,
    /// and `false` otherwise.
    fn exists(self) -> bool {
        match self.width {
            8 | 16 | 32 | 64 | 128 => true,
            _ => false,
        }
    }

    fn as_path(self) -> syn::TypePath {
        syn::TypePath {
            qself: None,
            path: [format!("u{}", self.width)].into_iter().collect(),
        }
    }
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

    /// Devises a 'const check' strategy.
    ///
    /// This produces an expression of the form:
    ///
    /// ```no_run
    /// if #expected_width != #actual_width {
    ///     ::core::panicking::panic(/* panic message */);
    /// }
    /// ```
    fn const_check(expected_width: usize, actual_width: &Width) -> Self {
        let span = actual_width.span();

        // FIXME: print item ident so the user knows that the heck we're talking about
        let panic_msg = format!("item width should be {expected_width}");

        let expected_width = syn::ExprLit {
            attrs: Vec::new(),
            lit: syn::LitInt::new(&expected_width.to_string(), span).into(),
        };
        let condition = syn::ExprBinary {
            attrs: Vec::new(),
            left: Box::new(expected_width.into()),
            op: syn::BinOp::Ne(syn::Token![!=](span)),
            right: Box::new(actual_width.into_expr()),
        };

        let panic_path = syn::Path {
            leading_colon: Some(syn::Token![::](span)),
            segments: ["core", "panicking", "panic"]
                .map(|it| syn::PathSegment {
                    ident: syn::Ident::new(it, span),
                    arguments: syn::PathArguments::None,
                })
                .into_iter()
                .collect(),
        };
        let panic_arg = syn::Expr::Lit(syn::ExprLit {
            attrs: Vec::new(),
            lit: syn::LitStr::new(&panic_msg, span).into(),
        });
        let panic_stmt = syn::Stmt::Expr(
            syn::ExprCall {
                attrs: Vec::new(),
                func: Box::new(
                    syn::ExprPath {
                        attrs: Vec::new(),
                        qself: None,
                        path: panic_path,
                    }
                    .into(),
                ),
                paren_token: syn::token::Paren(span),
                args: [panic_arg].into_iter().collect(),
            }
            .into(),
            Some(syn::Token![;](span)),
        );

        Self::ConstCheck(
            syn::ExprIf {
                attrs: Vec::new(),
                if_token: syn::Token![if](span),
                cond: Box::new(condition.into()),
                then_branch: syn::Block {
                    brace_token: syn::token::Brace(span),
                    stmts: vec![panic_stmt],
                },
                else_branch: None,
            }
            .into(),
        )
    }
}

/// Returns the best representation for an item.
///
/// If `item_attrs` contains a `repr` attribute, its argument is parsed as a [`UIntType`]. If
/// successful, the attribute is first removed from `item_attrs` so it will not appear in the
/// generated item, and then the attribute argument is returned.
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
        let (ty, span) = match attr.parse_args::<syn::Ident>() {
            Ok(it) => (it.to_string(), it.span()),
            Err(e) => {
                return Err(Error(e));
            }
        };
        let repr = match UIntType::parse(span, &ty) {
            Some(Ok(it)) => {
                if !it.exists() {
                    return Err(err!(span; "attribute argument cannot be an imaginary type"));
                }

                it
            }
            Some(Err(e)) => {
                return Err(e);
            }
            None => {
                return Err(err!(span; "attribute argument must be an unsigned integer primitive"));
            }
        };
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
                "item cannot be represented by any unsigned integer primitive",
            ));
        }

        Ok(repr)
    }
}

struct Output {
    item: syn::Item,
    item_impl: syn::ItemImpl,
    ident: syn::Ident,
    width: Width,
    repr: UIntType,
    from_repr_unchecked_block: syn::Block,
    from_repr_checked_block: syn::Block,
    to_repr_block: syn::Block,
}

impl Output {
    fn into_token_stream(self) -> TokenStream2 {
        let mut stream = self.item.into_token_stream();
        stream.extend_one(self.item_impl);
        stream.extend_one(self.make_bitwise_impl());

        stream
    }

    fn make_bitwise_impl(&self) -> syn::ItemImpl {
        // FIXME: span
        let span = self.item.span();

        let repr_ident = syn::Ident::new("repr", span);

        let and_token = syn::Token![&](span);
        let brace_token = syn::token::Brace(span);
        let colon_token = syn::Token![:](span);
        let const_token = syn::Token![const](span);
        let eq_token = syn::Token![=](span);
        let fn_token = syn::Token![fn](span);
        let for_token = syn::Token![for](span);
        let gt_token = syn::Token![>](span);
        let impl_token = syn::Token![impl](span);
        let lt_token = syn::Token![<](span);
        let paren_token: syn::token::Paren = syn::token::Paren(span);
        let path_sep_token = syn::Token![::](span);
        let r_arrow_token = syn::Token![->](span);
        let self_token = syn::Token![self](span);
        let semi_token = syn::Token![;](span);
        let type_token = syn::Token![type](span);
        let unsafe_token = syn::Token![unsafe](span);

        let trait_path = syn::Path {
            leading_colon: Some(path_sep_token),
            segments: ["regent", "Bitwise"]
                .map(|it| syn::PathSegment {
                    ident: syn::Ident::new(it, span),
                    arguments: syn::PathArguments::None,
                })
                .into_iter()
                .collect(),
        };

        let item_ty = syn::TypePath {
            qself: None,
            path: [self.ident].into_iter().collect(),
        }
        .into();
        let option_item_ty = syn::TypePath {
            qself: None,
            path: syn::Path {
                leading_colon: Some(path_sep_token),
                segments: ["core", "option"]
                    .into_iter()
                    .map(syn::PathSegment::from)
                    .chain([syn::PathSegment {
                        ident: syn::Ident::new("Option", span),
                        arguments: syn::AngleBracketedGenericArguments {
                            colon2_token: None,
                            lt_token,
                            args: [item_ty].into_iter().collect(),
                            gt_token,
                        }
                        .into(),
                    }])
                    .collect(),
            },
        }
        .into();
        let repr_ty = self.repr.as_path().into();

        let width_item = syn::ImplItemConst {
            attrs: Vec::new(),
            vis: syn::Visibility::Inherited,
            defaultness: None,
            const_token,
            ident: syn::Ident::new("WIDTH", span),
            generics: Default::default(),
            colon_token,
            ty: syn::TypePath {
                qself: None,
                path: ["usize"].into_iter().collect(),
            }
            .into(),
            eq_token,
            expr: self.width.into_expr(),
            semi_token,
        }
        .into();

        let repr_item = syn::ImplItemType {
            attrs: Vec::new(),
            vis: syn::Visibility::Inherited,
            defaultness: None,
            type_token,
            ident: repr_ident,
            generics: Default::default(),
            eq_token,
            ty: repr_ty.clone(),
            semi_token,
        }
        .into();

        let self_arg = syn::FnArg::Receiver(syn::Receiver {
            attrs: Vec::new(),
            reference: Some((and_token, None)),
            mutability: None,
            self_token,
            colon_token: None,
            ty: Box::new(item_ty),
        });
        let repr_arg = syn::FnArg::Typed(syn::PatType {
            attrs: Vec::new(),
            pat: syn::PatPath {
                attrs: Vec::New(),
                qself: None,
                path: [repr_ident].into_iter().collect(),
            }
            .into(),
            colon_token,
            ty: Box::new(repr_ty),
        });

        let fn_items = [
            (
                syn::Signature {
                    constness: None,
                    asyncness: None,
                    unsafety: Some(unsafe_token),
                    abi: None,
                    fn_token,
                    ident: syn::Ident::new("from_repr_unchecked", span),
                    generics: Default::default(),
                    paren_token,
                    inputs: [repr_arg].into_iter().collect(),
                    variadic: None,
                    output: syn::ReturnType::Type(r_arrow_token, Box::new(item_ty)),
                },
                self.from_repr_unchecked_block,
            ),
            (
                syn::Signature {
                    constness: None,
                    asyncness: None,
                    unsafety: None,
                    abi: None,
                    fn_token,
                    ident: syn::Ident::new("from_repr_checked", span),
                    generics: Default::default(),
                    paren_token,
                    inputs: [repr_arg].into_iter().collect(),
                    variadic: None,
                    output: syn::ReturnType::Type(r_arrow_token, Box::new(option_item_ty)),
                },
                self.from_repr_checked_block,
            ),
            (
                syn::Signature {
                    constness: None,
                    asyncness: None,
                    unsafety: None,
                    abi: None,
                    fn_token,
                    ident: syn::Ident::new("to_repr", span),
                    generics: Default::default(),
                    paren_token,
                    inputs: [self_arg].into_iter().collect(),
                    variadic: None,
                    output: syn::ReturnType::Type(r_arrow_token, Box::new(repr_ty)),
                },
                self.to_repr_block,
            ),
        ]
        .into_iter()
        .map(|(sig, block)| {
            syn::ImplItemFn {
                attrs: Vec::new(),
                vis: syn::Visibility::Inherited,
                defaultness: None,
                sig,
                block,
            }
            .into()
        });

        let items = [width_item, repr_item]
            .into_iter()
            .chain(fn_items)
            .collect();

        syn::ItemImpl {
            attrs: Vec::new(),
            defaultness: None,
            unsafety: None,
            impl_token,
            generics: Default::default(),
            trait_: Some((None, trait_path, for_token)),
            self_ty: Box::new(item_ty),
            brace_token,
            items,
        }
    }
}
