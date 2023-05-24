// SPDX-License-Identifier: MPL-2.0

//! Implementation details for [Regent].
//!
//! This crate provides the [`bitwise!`] attribute macro that is re-exported by the main *regent*
//! crate.
//!
//! [Regent]: https://crates.io/crates/regent

#![deny(rustdoc::broken_intra_doc_links, rustdoc::private_intra_doc_links)]
#![cfg_attr(feature = "nightly", feature(proc_macro_span))]

/// A type alias for [`Result<T, E>`] where `E` is [`Error`].
///
/// [`Result<T, E>`]: std::result::Result
type Result<T> = std::result::Result<T, Error>;

/// The error type returned by fallible functions in *regent-internals*.
///
/// This is a wrapper over [`syn::Error`] and is convertible into [`TokenStream`] via a [`From`]
/// implementation.
struct Error(syn::Error);

impl From<Error> for TokenStream {
    fn from(e: Error) -> Self {
        e.0.into_compile_error().into()
    }
}

/// Creates an [`Error`] with the given message and, optionally, span.
///
/// The syntax of this macro is similar to that of [`format!`] except that:
///
/// - [named parameters] (e.g., `var = 5`) are not allowed in the format argument list; and
/// - the format string may be preceded by a span expression and semicolon (e.g., `span;`).
///
/// The format string and format arguments are passed verbatim to `format!` to produce the error
/// message. The span of the error message is the span expression, if present, or
/// [`Span2::call_site`] otherwise.
///
/// [named parameters]: https://doc.rust-lang.org/std/fmt/index.html#named-parameters
///
/// # Examples
///
/// Named parameter referencing a local variable:
///
/// ```ignore
/// # fn main() -> Result<(), Error> {
/// let ident: syn::Ident;
/// # ident = syn::Ident::new("_", Span2::call_site());
/// return Err(err!("argument `{ident}` must be an integer literal"));
/// # }
/// ```
///
/// Positional parameter referencing a format argument:
///
/// ```ignore
/// # fn main() -> Result<(), Error> {
/// let span: Span2;
/// # span = Span2::call_site();
/// let item: syn::ItemEnum;
/// # item = syn::ItemEnum {
/// #     attrs: vec![],
/// #     vis: syn::Visibility::Inherited,
/// #     enum_token: Default::default(),
/// #     ident: syn::Ident::new("_", span),
/// #     generics: Default::default(),
/// #     brace_token: Default::default(),
/// #     variants: Default::default(),
/// # };
/// return Err(err!(span; "enum `{}` must have at least one variant", item.ident));
/// # }
macro_rules! err {
    ($fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        err!(Span2::call_site(); $fmt $(, $fmt_arg)*)
    };
    ($span:expr ; $fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        Error(syn::Error::new($span, format!($fmt $(, $fmt_arg)*)))
    };
}

/// Creates a [`syn::Path`] from the given path and span.
///
/// This macro accepts a span expression, semicolon ';', and path, in that order.
///
/// # Examples
///
/// ```ignore
/// let span: Span2;
/// # span = Span2::call_site();
/// let paths: [syn::Path; 3] = [
///     path!(span; usize),
///     path!(span; Self::Repr),
///     path!(span; ::core::option::Option),
/// ];
/// ```
macro_rules! path {
    // Case for identifiers and paths without leading colons.
    ($span:expr ; $head_seg:ident $(:: $tail_seg:ident)*) => {
        path!(@internal => {
            span: $span,
            leading_colon: None,
            segments: $head_seg $($tail_seg)*,
        })
    };
    // Case for paths with leading colons `::`.
    ($span:expr ; :: $head_seg:ident $(:: $tail_seg:ident)*) => {
        path!(@internal => {
            span: $span,
            leading_colon: Some(syn::Token![::]($span)),
            segments: $head_seg $($tail_seg)*,
        })
    };
    // Implementation detail.
    (@internal => {
        span: $span:expr,
        leading_colon: $leading_colon:expr,
        segments: $($seg:ident)* $(,)?
    }) => {
        syn::Path {
            leading_colon: $leading_colon,
            segments: [$(stringify!($seg)),*]
                .into_iter()
                .map(|seg| syn::PathSegment::from(syn::Ident::new(seg, $span)))
                .collect(),
        }
    };
}

/// Creates an implementor of `From<syn::ExprPath>`.
///
/// This macro offers two syntaxes: one equivalent to [`path!`], and one that accepts an expression
/// implementing `Into<syn::Path>`.
///
/// The output is of the form `syn::ExprPath {/* ... */}.into()`. The concrete type of the
/// expression inferred from context.
macro_rules! expr_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::ExprPath { attrs: vec![], qself: None, path: path!($span; $($path_piece)*) }.into()
    };
    ($path:expr $(,)?) => {
        syn::ExprPath { attrs: vec![], qself: None, path: $path.into() }.into()
    }
}

/// Creates an implementor of `From<syn::PatPath>`.
///
/// This macro offers two syntaxes: one equivalent to [`path!`], and one that accepts an expression
/// implementing `Into<syn::Path>`.
///
/// The output is of the form `syn::PatPath {/* ... */}.into()`. The concrete type of the
/// expression inferred from context.
macro_rules! pat_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::PatPath { attrs: vec![], qself: None, path: path!($span; $($path_piece)*) }.into()
    };
    ($path:expr $(,)?) => {
        syn::PatPath { attrs: vec![], qself: None, path: $path.into() }.into()
    }
}

/// Creates an implementor of `From<syn::TypePath>`.
///
/// This macro offers two syntaxes: one equivalent to [`path!`], and one that accepts an expression
/// implementing `Into<syn::Path>`.
///
/// The output is of the form `syn::TypePath {/* ... */}.into()`. The concrete type of the
/// expression inferred from context.
macro_rules! ty_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::TypePath { qself: None, path: path!($span; $($path_piece)*) }.into()
    };
    ($path:expr $(,)?) => {
        syn::TypePath { qself: None, path: $path.into() }.into()
    }
}

/// Wraps an expression in a [`syn::Block`].
///
/// # Examples
///
/// ```ignore
/// let span: Span2;
/// # span = Span2::call_site();
/// // Rendered:
/// //   { Self::Repr }
/// let repr_block: syn::Block = blockify::<syn::Expr>(expr_path!(span; Self::Repr));
/// // Rendered:
/// //   { *ptr }
/// let deref_block: syn::Block = blockify(syn::ExprUnary {
///     attrs: vec![],
///     op: syn::UnOp::Deref(syn::Token![*](span)),
///     expr: Box::new(expr_path!(span; ptr)),
/// });
/// ```
fn blockify<E: Into<syn::Expr>>(expr: E) -> syn::Block {
    let expr = expr.into();

    syn::Block {
        brace_token: syn::token::Brace(expr.span()),
        stmts: vec![syn::Stmt::Expr(expr, None)],
    }
}

/// Wraps an expression in parentheses.
///
/// This function is used to enforce a particular order of operations in case the associativity of
/// the expression, and adjacent expressions, otherwise lends to an incorrect interpretation.
///
/// In particular, if the expression is
///
/// - an assignment (e.g., `a = b`);
/// - a binary operation (e.g., `a + b`);
/// - a cast (e.g., `x as u32`);
/// - a closure (e.g., `|| x`);
/// - a `let` guard (e.g., `let Some(a) = b`);
/// - a range (e.g., `a..b`);
/// - a reference (e.g., `&mut x`);
/// - a unary operation (e.g., `!a`); or
/// - or a `None`-delimited [group],
///
/// it is parenthesized. Otherwise, it is returned without modification.
fn parenthesize<E: Into<syn::Expr>>(expr: E) -> syn::Expr {
    let expr = expr.into();

    let needs_parens = matches!(
        expr,
        syn::Expr::Assign(_)
            | syn::Expr::Binary(_)
            | syn::Expr::Cast(_)
            | syn::Expr::Closure(_)
            | syn::Expr::Group(_)
            | syn::Expr::Let(_)
            | syn::Expr::Range(_)
            | syn::Expr::Reference(_)
            | syn::Expr::Unary(_),
    );
    if !needs_parens {
        return expr;
    }

    syn::ExprParen {
        attrs: vec![],
        paren_token: syn::token::Paren(expr.span()),
        expr: Box::new(expr),
    }
    .into()
}

/// Creates a bit-mask of the form:
///
/// ```ignore
/// (!0 >> (#repr_width - #width))
/// ```
fn mask(repr_width: Width, width: Width) -> syn::Expr {
    let span = width.span();

    let lhs = syn::ExprUnary {
        attrs: vec![],
        op: syn::UnOp::Not(syn::Token![!](span)),
        expr: Box::new(
            syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("0", span).into() }.into(),
        ),
    }
    .into();
    let rhs = parenthesize(syn::ExprBinary {
        attrs: vec![],
        left: Box::new(repr_width.parenthesize().into()),
        op: syn::BinOp::Sub(syn::Token![-](span)),
        right: Box::new(width.parenthesize().into()),
    });

    parenthesize(syn::ExprBinary {
        attrs: vec![],
        left: Box::new(lhs),
        op: syn::BinOp::Shr(syn::Token![>>](span)),
        right: Box::new(rhs),
    })
}

mod forms;
mod receiver;
mod sig;
mod uint;
mod width;

use std::{fmt, iter::once};

use forms::*;
use proc_macro::TokenStream;
use proc_macro2::Span as Span2;
use receiver::Receiver;
use syn::{__private::ToTokens, parse::Parser as _, punctuated::Punctuated, spanned::Spanned as _};
use width::*;

/// The whole point.
///
/// Refer to the `spec` module in the crate root for usage information.
#[proc_macro_attribute]
pub fn bitwise(args: TokenStream, item: TokenStream) -> TokenStream {
    let args = match Args::parse(args) {
        Ok(it) => it,
        Err(e) => {
            return e.into();
        }
    };
    let expected_width = args.expected_width();

    macro_rules! form {
        ($ty:ty : $item:expr) => {
            <$ty>::bitwise($item).and_then(|output| output.try_into_token_stream(expected_width))
        };
    }

    let result = match syn::parse_macro_input!(item as _) {
        syn::Item::Struct(item) => form!(Struct: item),
        syn::Item::Enum(item) => form!(Enum: item),
        item => Err(err!(item.span(); "item must be a struct or enum")),
    };

    match result {
        Ok(it) => it,
        Err(e) => e.into(),
    }
}

/// Models acceptable arguments to the `#[bitwise]` attribute.
#[derive(Default)]
struct Args {
    /// The `size` argument, if present.
    ///
    /// This determines the size, in bytes, of the emitted item. This argument is
    /// mutually-exclusive with the [`width`] argument.
    ///
    /// [`width`]: Self::width
    size: Option<usize>,
    /// The `width` argument, if present.
    ///
    /// This determines the width, in bits, of the emitted item. This argument is
    /// mutually-exclusive with the [`size`] argument.
    ///
    /// [`size`]: Self::size
    width: Option<usize>,
}

impl Args {
    /// Parses comma-separated arguments to the `#[bitwise]` attribute from the given
    /// [`TokenStream`].
    ///
    /// # Errors
    ///
    /// An error is returned if any argument
    ///
    /// - is not of the form `"name" "=" "value"` (ABNF);
    /// - has a name other than `size` or `width`;
    /// - has the same name as a previous argument; or
    /// - has a value that is not an integer literal.
    ///
    /// Also, an error is returned if both the `size` and `width` arguments are present.
    fn parse(args: TokenStream) -> Result<Self> {
        let mut output = Self::default();

        if args.is_empty() {
            return Ok(output);
        }

        syn::meta::parser(|meta| {
            let ident = meta.path.get_ident().ok_or_else(|| -> syn::Error {
                syn::Error::new(meta.path.span(), "argument path must be an identifier")
            })?;
            let arg = if ident == "size" {
                &mut output.size
            } else if ident == "width" {
                &mut output.width
            } else {
                return Err(meta.error("argument is not supported"));
            };
            if arg.is_some() {
                return Err(meta.error("argument is a duplicate"));
            }
            let value = meta
                .value()
                .and_then(|it| it.parse::<syn::LitInt>())
                .and_then(|it| it.base10_parse())?;
            *arg = Some(value);

            Ok(())
        })
        .parse(args)
        .map_err(Error)?;

        if output.size.is_some() && output.width.is_some() {
            return Err(err!("`size` and `width` arguments are mutually exclusive"));
        }

        Ok(output)
    }

    /// The expected bit-width, if any, of the emitted item.
    ///
    /// If [`Some`], this value represents the user's expectation of the minimum number of bits
    /// necessary to represent all struct fields or enum variants&mdash;whichever it is&mdash;for
    /// the emitted item. [`bitwise!`] must emit an error if the expected width does not match the
    /// actual width of the item.
    fn expected_width(&self) -> Option<usize> {
        self.width.or(self.size.map(|it| it * 8))
    }
}

/// Implements one form of the [`bitwise!`] macro.
trait Form {
    /// The kind of item that this form of [`bitwise!`] operates on.
    type Item;

    /// A form of [`bitwise!`].
    fn bitwise(item: Self::Item) -> Result<Output<Self::Item>>;
}

/// The output of [`Form::bitwise`].
struct Output<Item> {
    // Statements to be executed in a `const` context at the global scope.
    const_ctx: Vec<syn::Stmt>,
    /// The emitted item.
    item: Item,
    /// The <code>impl&nbsp;<em>item</em></code> [impl block] for [the emitted item].
    ///
    /// [impl block]: syn::ItemImpl
    /// [the emitted item]: Self::item
    impl_item: Option<syn::ItemImpl>,
    /// The implementation of the `Bitwise` trait for [the emitted item].
    ///
    /// [the emitted item]: Self::item
    impl_bitwise_for_item: BitwiseImpl,
}

impl<Item: ToTokens> Output<Item> {
    /// Attempts to convert this into a [`TokenStream`].
    ///
    /// # Arguments
    ///
    /// `expected_width` corresponds to [`Args::expected_width`].
    ///
    /// # Errors
    ///
    /// An error is returned if `expected_width` differs from
    /// [`self.impl_bitwise_for_item.width`][actual width].
    ///
    /// [actual width]: BitwiseImpl::width
    fn try_into_token_stream(mut self, expected_width: Option<usize>) -> Result<TokenStream> {
        if let Some(expected_width) = expected_width {
            match EnforceItemWidthStrategy::devise(
                &self.impl_bitwise_for_item.ident,
                expected_width,
                self.impl_bitwise_for_item.width.clone(),
            ) {
                EnforceItemWidthStrategy::Fail(e) => {
                    return Err(e);
                }
                EnforceItemWidthStrategy::None => {}
                EnforceItemWidthStrategy::ConstCheck(expr) => {
                    self.const_ctx.push(syn::Stmt::Expr(expr, None));
                }
            }
        }

        let item_span = self.item.span();
        // This is an optional item containing a block to be executed in a `const` context at the
        // global scope.
        let const_check_item = Self::make_const_ctx_item(item_span, self.const_ctx);
        let impl_bitwise_for_item = self.impl_bitwise_for_item.into_item_impl(item_span);

        /// Constructs an array of [`TokenStream`]s from the given list of [`ToTokens`]
        /// implementors.
        macro_rules! make_token_streams {
            ($($to_tokens:expr),* $(,)?) => {
                [ $( TokenStream::from($to_tokens.into_token_stream()) ),* ]
            };
        }

        Ok(TokenStream::from_iter(make_token_streams![
            const_check_item,
            self.item,
            self.impl_item,
            impl_bitwise_for_item,
        ]))
    }
}

impl<Item> Output<Item> {
    fn make_const_ctx_item(item_span: Span2, const_ctx: Vec<syn::Stmt>) -> Option<syn::ItemConst> {
        let has_const_ctx = !const_ctx.is_empty();

        has_const_ctx.then(|| {
            let span = item_span;
            let unit_ty =
                syn::TypeTuple { paren_token: syn::token::Paren(span), elems: Punctuated::new() }
                    .into();
            let expr = syn::ExprBlock {
                attrs: vec![],
                label: None,
                block: syn::Block { brace_token: syn::token::Brace(span), stmts: const_ctx },
            }
            .into();

            // Rendered:
            //   const _: () = {/* self.const_ctx */};
            //
            // This trick forces `expr` to be evaluated at compile-time.
            syn::ItemConst {
                attrs: vec![],
                vis: syn::Visibility::Inherited,
                const_token: syn::Token![const](span),
                ident: syn::Ident::new("_", span),
                generics: Default::default(),
                colon_token: syn::Token![:](span),
                ty: Box::new(unit_ty),
                eq_token: syn::Token![=](span),
                expr: Box::new(expr),
                semi_token: syn::Token![;](span),
            }
        })
    }
}

/// A strategy to enforce the [expected bit-width] of an item.
///
/// [expected bit-width]: Args::expected_width
enum EnforceItemWidthStrategy {
    /// The expected width is correct, and nothing needs to be done.
    None,
    /// The expected width is incorrect, and this error should be returned during macro evaluation.
    Fail(Error),
    /// The correctness of the expected width is indeterminate at macro evaluation time, so this
    /// expression should be inserted in a `const` context to perform the check at compile-time.
    ConstCheck(syn::Expr),
}

impl EnforceItemWidthStrategy {
    /// Devises an `EnforceItemWidthStrategy`.
    ///
    /// The [`bitwise!`] macro accepts [`size`] and [`width`] [attribute arguments] which are
    /// intended to make compile-time guarantees about the `Bitwise::WIDTH` of the emitted item. In
    /// the simple case, the item width is [calculated exactly during macro evaluation], allowing
    /// `#![bitwise]` to emit an error if it differs from the expected width.
    ///
    /// However, if the item is a struct containing [custom implementors of `Bitwise`], the exact
    /// width cannot be known by the `#![bitwise]` macro. In that case, it emits an assertion in a
    /// `const` context to defer enforcement of the expected width to compile-time.
    ///
    /// This function is responsible for selecting one of these two approaches based on the item
    /// width. [`None`] is returned if the item width is determinate at macro evaluation time and
    /// equals the expected width; [`Fail`] is returned if it differs from the expected width; and
    /// [`ConstCheck`] is returned if the item width depends on compile-time information.
    ///
    /// [`size`]: Args::size
    /// [`width`]: Args::width
    /// [attribute arguments]: Args
    /// [calculated exactly during macro evaluation]: Width::Met
    /// [custom implementors of `Bitwise`]: forms::r#struct::field::ElemType::ImplBitwise
    /// [`None`]: Self::None
    /// [`Fail`]: Self::Fail
    /// [`ConstCheck`]: Self::ConstCheck
    ///
    /// # Arguments
    ///
    /// `item_ident` is the name of the item and is used to generate precise error messages.
    /// `expected_width` corresponds to [`Args::expected_width`], and `actual_width` is the computed
    /// bit-width of the item.
    pub(crate) fn devise(
        item_ident: impl fmt::Display,
        expected_width: usize,
        actual_width: Width,
    ) -> Self {
        match actual_width {
            Width::Met(span, actual_width) => {
                if expected_width != actual_width {
                    return Self::Fail(err!(
                        span;
                        "item width is {actual_width} bits, should be {expected_width}",
                    ));
                }

                Self::None
            }
            Width::Ct(actual_width) => Self::const_check(item_ident, expected_width, actual_width),
        }
    }

    /// Devises a 'const check' strategy.
    ///
    /// This produces an expression of the form:
    ///
    /// ```ignore
    /// assert_eq!(#expected_width, #actual_width, /* panic message */)
    /// ```
    ///
    /// # Arguments
    ///
    /// All arguments are the same as [`devise`].
    ///
    /// [`devise`]: Self::devise
    fn const_check(
        item_ident: impl fmt::Display,
        expected_width: usize,
        actual_width: syn::Expr,
    ) -> Self {
        let span = actual_width.span();
        let actual_width = parenthesize(actual_width);

        let mut error_msg = format!(
            "width of item `{item_ident}` should be {expected_width} bits but is actually {}",
            actual_width.to_token_stream(),
        );
        // TODO: remove this nightly feature gate when `proc_macro_span` is stabilized
        #[cfg(feature = "nightly")]
        {
            let span = span.unwrap();
            let filepath = span.source_file().path();
            let start = span.start();
            error_msg.push_str(&format!(
                "\nthis error originated from {filepath}, {line}:{column}",
                filepath = filepath.display(),
                line = start.line,
                column = start.column,
            ));
        }
        let error_msg =
            syn::ExprLit { attrs: vec![], lit: syn::LitStr::new(&error_msg, span).into() }.into();

        let expected_width = syn::ExprLit {
            attrs: vec![],
            lit: syn::LitInt::new(&expected_width.to_string(), span).into(),
        }
        .into();
        let args: Punctuated<syn::Expr, syn::Token![,]> =
            Punctuated::from_iter([expected_width, actual_width, error_msg]);
        let mac = syn::Macro {
            path: path!(span; assert_eq),
            bang_token: syn::Token![!](span),
            delimiter: syn::MacroDelimiter::Paren(syn::token::Paren(span)),
            tokens: args.into_token_stream(),
        };

        Self::ConstCheck(syn::ExprMacro { attrs: vec![], mac }.into())
    }
}

/// An implementation of the `Bitwise` trait.
struct BitwiseImpl {
    /// The name of the implementor.
    ident: syn::Ident,
    /// The bit-width of the implementor.
    width: Width,
    /// The [internal representation], or storage type, of the implementor.
    ///
    /// [internal representation]: uint::RustType::repr_for_item
    repr: uint::RustType,
    /// The associated function implementations.
    funcs: BitwiseFuncs,
}

impl BitwiseImpl {
    /// Converts this into a [`syn::ItemImpl`] with the given span.
    fn into_item_impl(self, span: Span2) -> syn::ItemImpl {
        let brace_token = syn::token::Brace(span);
        let colon_token = syn::Token![:](span);
        let const_token = syn::Token![const](span);
        let eq_token = syn::Token![=](span);
        let for_token = syn::Token![for](span);
        let impl_token = syn::Token![impl](span);
        let semi_token = syn::Token![;](span);
        let type_token = syn::Token![type](span);

        // Rendered:
        //   const WIDTH: usize = /* self.width */;
        let width_item = syn::ImplItemConst {
            attrs: vec![],
            vis: syn::Visibility::Inherited,
            defaultness: None,
            const_token,
            ident: syn::Ident::new("WIDTH", span),
            generics: Default::default(),
            colon_token,
            ty: ty_path!(span; usize),
            eq_token,
            expr: self.width.into(),
            semi_token,
        }
        .into();
        // Rendered:
        //   type Repr = /* self.repr */;
        let repr_item = syn::ImplItemType {
            attrs: vec![],
            vis: syn::Visibility::Inherited,
            defaultness: None,
            type_token,
            ident: syn::Ident::new("Repr", span),
            generics: Default::default(),
            eq_token,
            ty: self.repr.into_syn_type(span),
            semi_token,
        }
        .into();

        let items = [width_item, repr_item]
            .into_iter()
            .chain(self.funcs.into_iter().map(syn::ImplItem::Fn))
            .collect();

        // Rendered:
        //   impl ::regent::Bitwise for /* self.ident */ {
        //       #width_item
        //       #repr_item
        //       /* self.funcs */
        //   }
        syn::ItemImpl {
            attrs: vec![],
            defaultness: None,
            unsafety: None,
            impl_token,
            generics: Default::default(),
            trait_: Some((None, path!(span; ::regent::Bitwise), for_token)),
            self_ty: Box::new(ty_path!(self.ident)),
            brace_token,
            items,
        }
    }
}

/// Associated function implementations for the `Bitwise` trait.
///
/// This struct consists of [`syn::Block`]s rather than [`syn::ItemFn`]s because the function
/// signatures can be inferred from context.
struct BitwiseFuncs {
    /// The block for the `from_repr_unchecked` function.
    from_repr_unchecked: syn::Block,
    /// The block for the `from_repr_checked` function.
    from_repr_checked: syn::Block,
    /// The block for the `to_repr` function.
    to_repr: syn::Block,
    /// The block for the `into_repr` function.
    into_repr: syn::Block,
}

impl BitwiseFuncs {
    /// Converts this into an iterator of [`syn::ImplItemFn`]s.
    fn into_iter(self) -> impl Iterator<Item = syn::ImplItemFn> {
        /// Creates a [`syn::Signature`] and [`syn::Block`] pair.
        ///
        /// # Arguments
        ///
        /// `builder` is an expression of type [`sig::Builder`]. `inputs` and `output` are forwarded
        /// to [`sig::Builder::build`] and described there. `block` is the name of the function as
        /// an identifier.
        macro_rules! make_fn {
            (
                builder: $builder:expr,
                inputs: $inputs:expr,
                output: $output:expr,
                block: $block:ident $(,)?
            ) => {{
                let span = self.$block.span();
                let sig = $builder.build(
                    span,
                    syn::Ident::new(stringify!($block), span),
                    $inputs,
                    $output,
                );

                (sig, self.$block)
            }};
        }

        /// Produces a [`syn::PatType`] of the form `repr: Self::Repr` with the given span.
        fn make_repr_arg(span: Span2) -> syn::PatType {
            syn::PatType {
                attrs: vec![],
                pat: Box::new(pat_path!(span; repr)),
                colon_token: syn::Token![:](span),
                ty: Box::new(ty_path!(span; Self::Repr)),
            }
        }

        /// Produces a [`syn::Type`] of the form `::core::option::Option::<Self>` with the given
        /// span.
        fn make_option_self_ty(span: Span2) -> syn::Type {
            let tail = syn::PathSegment {
                ident: syn::Ident::new("Option", span),
                arguments: syn::PathArguments::AngleBracketed(
                    syn::AngleBracketedGenericArguments {
                        colon2_token: Some(syn::Token![::](span)),
                        lt_token: syn::Token![<](span),
                        args: once(syn::GenericArgument::Type(ty_path!(span; Self))).collect(),
                        gt_token: syn::Token![>](span),
                    },
                ),
            };
            let segments = ["core", "option"]
                .into_iter()
                .map(|it| syn::Ident::new(it, span).into())
                .chain([tail])
                .collect();

            syn::TypePath {
                qself: None,
                path: syn::Path { leading_colon: Some(syn::Token![::](span)), segments },
            }
            .into()
        }

        [
            // Rendered:
            //   unsafe fn from_repr_unchecked(repr: Self::Repr) -> Self
            make_fn! {
                builder: sig::Builder::new().with_unsafe(),
                inputs: |span| [make_repr_arg(span)],
                output: |span| Some(ty_path!(span; Self)),
                block: from_repr_unchecked,
            },
            // Rendered:
            //   fn from_repr_checked(repr: Self::Repr) -> ::core::option::Option::<Self>
            make_fn! {
                builder: sig::Builder::new(),
                inputs: |span| [make_repr_arg(span)],
                output: |span| Some(make_option_self_ty(span)),
                block: from_repr_checked,
            },
            // Rendered:
            //   fn to_repr(&self) -> Self::Repr
            make_fn! {
                builder: sig::Builder::new().with_receiver(Receiver::new_ref_self()),
                inputs: |_| [],
                output: |span| Some(ty_path!(span; Self::Repr)),
                block: to_repr,
            },
            // Rendered:
            //   fn into_repr(self) -> Self::Repr
            make_fn! {
                builder: sig::Builder::new().with_receiver(Receiver::new_self()),
                inputs: |_| [],
                output: |span| Some(ty_path!(span; Self::Repr)),
                block: into_repr,
            },
        ]
        .into_iter()
        .map(|(sig, block)| syn::ImplItemFn {
            attrs: vec![],
            vis: syn::Visibility::Inherited,
            defaultness: None,
            sig,
            block,
        })
    }
}
