// SPDX-License-Identifier: MPL-2.0

//! Procedural macro implementations for [Regent](https://crates.io/crates/regent).
//!
//! This crate provides the [`bitwise`] proc macro that is re-exported by the main *regent* crate.

/// The error type returned by fallible functions in *regent-internals*.
///
/// This is a wrapper over [`syn::Error`] and is convertible into [`TokenStream`].
struct Error(syn::Error);

impl From<Error> for TokenStream {
    fn from(e: Error) -> Self {
        e.0.into_compile_error().into()
    }
}

/// Creates an [`Error`] with the given message and, optionally, span.
///
/// If no span is specified, [`call_site`](Span2::call_site) is used.
macro_rules! err {
    ($fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        err!(Span2::call_site();  $fmt $(, $fmt_arg)*)
    };
    ($span:expr ; $fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        Error(syn::Error::new($span, format!($fmt $(, $fmt_arg)*)))
    };
}

/// Creates a [`syn::Path`] from the given path and span.
macro_rules! path {
    ($span:expr ; $head_seg:ident $(:: $tail_seg:ident)*) => {
        path!(@internal => {
            span: $span,
            leading_colon: None,
            segments: $head_seg $($tail_seg)*,
        })
    };
    ($span:expr ; :: $head_seg:ident $(:: $tail_seg:ident)*) => {
        path!(@internal => {
            span: $span,
            leading_colon: Some(syn::Token![::]($span)),
            segments: $head_seg $($tail_seg)*,
        })
    };
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

/// Creates an implementor of `From<syn::ExprPath>` from the given path and span.
///
/// The concrete type of the result is inferred from context.
///
/// This macro offers two syntaxes: one compatible with [`path`], and one that accepts an
/// implementor of `Into<syn::Path>`.
macro_rules! expr_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::ExprPath { attrs: vec![], qself: None, path: path!($span; $($path_piece)*) }.into()
    };
    ($path:expr $(,)?) => {
        syn::ExprPath { attrs: vec![], qself: None, path: $path.into() }.into()
    }
}

/// Creates an implementor of `From<syn::PatPath>` from the given path and span.
///
/// The concrete type of the result is inferred from context.
///
/// This macro offers two syntaxes: one compatible with [`path`], and one that accepts an
/// implementor of `Into<syn::Path>`.
macro_rules! pat_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::PatPath { attrs: vec![], qself: None, path: path!($span; $($path_piece)*) }.into()
    };
    ($path:expr $(,)?) => {
        syn::PatPath { attrs: vec![], qself: None, path: $path.into() }.into()
    }
}

/// Creates an implementor of `From<syn::TypePath>` from the given path and span.
///
/// The concrete type of the result is inferred from context.
///
/// This macro offers two syntaxes: one compatible with [`path`], and one that accepts an
/// implementor of `Into<syn::Path>`.
macro_rules! type_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::TypePath { qself: None, path: path!($span; $($path_piece)*) }.into()
    };
    ($path:expr $(,)?) => {
        syn::TypePath { qself: None, path: $path.into() }.into()
    }
}

mod checks;
mod forms;
mod receiver;
mod sig;
mod uint;
mod width;

use std::iter::once;

use checks::*;
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

/// Acceptable arguments to the `#[bitwise]` attribute.
#[derive(Default)]
struct Args {
    /// The `size` argument, if any.
    ///
    /// This determines the size, in bytes, of the emitted item. This argument is
    /// mutually-exclusive with the [`width`](Self::width) argument.
    size: Option<usize>,
    /// The `width` argument, if any.
    ///
    /// This determines the width, in bits, of the emitted item. This argument is
    /// mutually-exclusive with the [`size`](Self::size) argument.
    width: Option<usize>,
}

impl Args {
    /// Parses comma-separated arguments to the `#[bitwise]` attribute from the given
    /// [`TokenStream`].
    fn parse(args: TokenStream) -> Result<Self, Error> {
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
    /// the emitted item. [`bitwise`] must emit an error if the expected width does not match the
    /// actual width of the item.
    fn expected_width(&self) -> Option<usize> {
        self.width.or_else(|| self.size.map(|it| it * 8))
    }
}

/// Implements one form of the [`bitwise`] macro.
trait Form {
    /// The kind of item that this form of [`bitwise`] operates on.
    type Item;

    /// A form of [`bitwise`].
    fn bitwise(item: Self::Item) -> Result<Output<Self::Item>, Error>;
}

/// The output of [`Form::bitwise`].
struct Output<Item> {
    /// The emitted item.
    item: Item,
    /// The <code>impl&nbsp;<em>item</em></code> [impl block](syn::ItemImpl) for [the emitted
    /// item](Self::item).
    impl_item: Option<syn::ItemImpl>,
    /// The implementation of the `Bitwise` trait for [the emitted item](Self::item).
    impl_bitwise_for_item: BitwiseImpl,
}

impl<Item: ToTokens> Output<Item> {
    /// Attempts to convert this into a [`TokenStream`].
    ///
    /// This method returns [`Err`] if the `expected_width` argument differs from
    /// [`self.impl_bitwise_for_item.width`](BitwiseImpl::width).
    ///
    /// # Arguments
    ///
    /// `expected_width` is the result of [`Args::expected_width`].
    fn try_into_token_stream(self, expected_width: Option<usize>) -> Result<TokenStream, Error> {
        // This is an optional item containing a block to be executed in a `const` context at the
        // global scope.
        //
        // When present, this block asserts at compile-time that `expected_width` equals
        // `self.impl_bitwise_for_item.width`.
        let mut const_check_item: Option<syn::ItemConst> = None;
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
                    let span = expr.span();
                    let unit_ty = syn::TypeTuple {
                        paren_token: syn::token::Paren(span),
                        elems: Punctuated::new(),
                    }
                    .into();
                    let block_expr = syn::ExprBlock {
                        attrs: vec![],
                        label: None,
                        block: syn::Block {
                            brace_token: syn::token::Brace(span),
                            stmts: vec![syn::Stmt::Expr(expr, None)],
                        },
                    }
                    .into();

                    // This looks like:
                    //   const _: () = { #expr };
                    //
                    // This trick forces `expr` to be evaluated at compile-time.
                    const_check_item = Some(syn::ItemConst {
                        attrs: vec![],
                        vis: syn::Visibility::Inherited,
                        const_token: syn::Token![const](span),
                        ident: syn::Ident::new("_", span),
                        generics: Default::default(),
                        colon_token: syn::Token![:](span),
                        ty: Box::new(unit_ty),
                        eq_token: syn::Token![=](span),
                        expr: Box::new(block_expr),
                        semi_token: syn::Token![;](span),
                    })
                }
            }
        }

        let impl_bitwise_for_item = self.impl_bitwise_for_item.into_item_impl(self.item.span());

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

/// An implementation of the `Bitwise` trait.
struct BitwiseImpl {
    /// The name of the implementor.
    ident: syn::Ident,
    /// The bit-width of the implementor.
    width: Width,
    /// The internal representation, or storage type, of the implementor.
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

        // const WIDTH: usize = /* self.width as expression */;
        let width_item = syn::ImplItemConst {
            attrs: vec![],
            vis: syn::Visibility::Inherited,
            defaultness: None,
            const_token,
            ident: syn::Ident::new("WIDTH", span),
            generics: Default::default(),
            colon_token,
            ty: type_path!(span; usize),
            eq_token,
            expr: self.width.into(),
            semi_token,
        }
        .into();
        // type Repr = /* self.repr as type */;
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

        // impl ::regent::Bitwise for /* self.ident as type */ {
        //     #width_item
        //     #repr_item
        //     /* self.funcs as list of function definitions */
        // }
        syn::ItemImpl {
            attrs: vec![],
            defaultness: None,
            unsafety: None,
            impl_token,
            generics: Default::default(),
            trait_: Some((None, path!(span; ::regent::Bitwise), for_token)),
            self_ty: Box::new(type_path!(self.ident)),
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
                ty: Box::new(type_path!(span; Self::Repr)),
            }
        }

        /// Produces a [`syn::Type`] of the form `::core::option::Option::<Self>` with the given
        /// span.
        fn make_option_self_ty(span: Span2) -> syn::Type {
            let segments = ["core", "option"]
                .into_iter()
                .map(|it| syn::Ident::new(it, span).into())
                .chain([syn::PathSegment {
                    ident: syn::Ident::new("Option", span),
                    arguments: syn::PathArguments::AngleBracketed(
                        syn::AngleBracketedGenericArguments {
                            colon2_token: Some(syn::Token![::](span)),
                            lt_token: syn::Token![<](span),
                            args: once(syn::GenericArgument::Type(type_path!(span; Self)))
                                .collect(),
                            gt_token: syn::Token![>](span),
                        },
                    ),
                }])
                .collect();

            syn::TypePath {
                qself: None,
                path: syn::Path { leading_colon: Some(syn::Token![::](span)), segments },
            }
            .into()
        }

        [
            make_fn! {
                builder: sig::Builder::new().with_unsafe(),
                inputs: |span| [make_repr_arg(span)],
                output: |span| Some(type_path!(span; Self)),
                block: from_repr_unchecked,
            },
            make_fn! {
                builder: sig::Builder::new(),
                inputs: |span| [make_repr_arg(span)],
                output: |span| Some(make_option_self_ty(span)),
                block: from_repr_checked,
            },
            make_fn! {
                builder: sig::Builder::new().with_receiver(Receiver::new_ref_self()),
                inputs: |_| [],
                output: |span| Some(type_path!(span; Self::Repr)),
                block: to_repr,
            },
            make_fn! {
                builder: sig::Builder::new().with_receiver(Receiver::new_self()),
                inputs: |_| [],
                output: |span| Some(type_path!(span; Self::Repr)),
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
