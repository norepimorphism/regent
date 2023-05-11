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

/// Creates an implementation of `From<syn::ExprPath>` from the given path and span.
///
/// The concrete type of the result is inferred from context.
///
/// The macro offers two syntaxes: one compatible with [`path`], and one that accepts a
/// path-convertible expression.
macro_rules! expr_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::ExprPath { attrs: vec![], qself: None, path: path!($span; $($path_piece)*) }.into()
    };
    ($path:expr $(,)?) => {
        syn::ExprPath { attrs: vec![], qself: None, path: $path.into() }.into()
    }
}

/// Creates an implementation of `From<syn::PatPath>` from the given path and span.
///
/// The concrete type of the result is inferred from context.
///
/// The macro offers two syntaxes: one compatible with [`path`], and one that accepts a
/// path-convertible expression.
macro_rules! pat_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::PatPath { attrs: vec![], qself: None, path: path!($span; $($path_piece)*) }.into()
    };
    ($path:expr $(,)?) => {
        syn::PatPath { attrs: vec![], qself: None, path: $path.into() }.into()
    }
}

/// Creates an implementation of `From<syn::TypePath>` from the given path and span.
///
/// The concrete type of the result is inferred from context.
///
/// The macro offers two syntaxes: one compatible with [`path`], and one that accepts a
/// path-convertible expression.
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
mod sum;
mod uint;

use std::iter::once;

use checks::*;
use forms::*;
use proc_macro::TokenStream;
use proc_macro2::Span as Span2;
use sum::*;
use syn::{__private::ToTokens, parse::Parser as _, punctuated::Punctuated, spanned::Spanned as _};

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

    match syn::parse_macro_input!(item as _) {
        syn::Item::Struct(item) => Struct::bitwise_as_token_stream(expected_width, item),
        syn::Item::Enum(item) => Enum::bitwise_as_token_stream(expected_width, item),
        item => err!(item.span(); "item must be a struct or enum").into(),
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
    /// If [`Some`], this bit-width represents the user's expectation of the minimum number of bits
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

trait FormExt: Form {
    /// A wrapper over [`Form::bitwise`] that maps the result to a [`TokenStream`].
    ///
    /// # Arguments
    ///
    /// `expected_width` is forwarded to [`Output::try_into_token_stream`]. `item` is forwarded to
    /// [`Form::bitwise`].
    fn bitwise_as_token_stream(expected_width: Option<usize>, item: Self::Item) -> TokenStream;
}

impl<T: Form> FormExt for T
where
    T::Item: ToTokens,
{
    fn bitwise_as_token_stream(expected_width: Option<usize>, item: Self::Item) -> TokenStream {
        let result =
            Self::bitwise(item).and_then(|output| output.try_into_token_stream(expected_width));

        match result {
            Ok(it) => it,
            Err(e) => e.into(),
        }
    }
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
    /// Attempts to render this as a [`TokenStream`].
    ///
    /// This method consumes `self`. It returns [`Err`] if the `expected_width` argument differs
    /// from [`self.impl_bitwise_for_item.width`](BitwiseImpl::width).
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
        let const_check_item = match expected_width {
            None => None,
            // This is where we enforce `expected_width`.
            //
            // FIXME: consider inverting control flow such that `EnforceItemWidthStrategy::devise`
            // leads into assigning a value to `const_check_item`.
            Some(expected_width) => match EnforceItemWidthStrategy::devise(
                expected_width,
                // FIXME: don't clone
                self.impl_bitwise_for_item.width.clone(),
            ) {
                EnforceItemWidthStrategy::None => None,
                EnforceItemWidthStrategy::Fail(e) => {
                    return Err(e);
                }
                EnforceItemWidthStrategy::ConstCheck(expr) => {
                    let span = expr.span();

                    // This looks like:
                    //   const _: () = { #expr };
                    //
                    // This trick forces `expr` to be evaluated at compile-time.
                    Some(syn::ItemConst {
                        attrs: vec![],
                        vis: syn::Visibility::Inherited,
                        const_token: syn::Token![const](span),
                        ident: syn::Ident::new("_", span),
                        generics: Default::default(),
                        colon_token: syn::Token![:](span),
                        ty: Box::new(
                            syn::TypeTuple {
                                paren_token: syn::token::Paren(span),
                                elems: Punctuated::new(),
                            }
                            .into(),
                        ),
                        eq_token: syn::Token![=](span),
                        expr: Box::new(
                            syn::ExprBlock {
                                attrs: vec![],
                                label: None,
                                block: syn::Block {
                                    brace_token: syn::token::Brace(span),
                                    stmts: vec![syn::Stmt::Expr(expr, None)],
                                },
                            }
                            .into(),
                        ),
                        semi_token: syn::Token![;](span),
                    })
                }
            },
        };

        let impl_bitwise_for_item = self.impl_bitwise_for_item.into_item_impl(self.item.span());

        /// Constructs an array of [`TokenStream`]s from the given list of [`ToTokens`]
        /// implementors.
        macro_rules! make_token_streams {
            ($($to_tokens:expr),* $(,)?) => {
                [ $( TokenStream::from($to_tokens.into_token_stream()) ),* ]
            };
        }

        let token_stream = make_token_streams![
            const_check_item,
            self.item,
            self.impl_item,
            impl_bitwise_for_item,
        ]
        .into_iter()
        .collect();

        Ok(token_stream)
    }
}

/// An implementation of the `Bitwise` trait.
struct BitwiseImpl {
    /// The name of the implementor.
    ident: syn::Ident,
    /// The bit-width of the implementor.
    width: Width,
    /// The internal representation, or backing storage, of the implementor.
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
            expr: self.width.into_expr(),
            semi_token,
        }
        .into();

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
        /// Models the receiver function argument: `self`, `&self`, or `&mut self`.
        struct Receiver {
            /// Whether or not this receiver is borrowed: `&self` or `&mut self`.
            is_borrowed: bool,
            /// Whether or not this receiver is mutable: `mut self` or `&mut self`.
            is_mutable: bool,
        }

        impl Receiver {
            /// Converts this into a [`syn::FnArg`] with the given span.
            fn into_arg(self, span: Span2) -> syn::FnArg {
                let mut_token = self.is_mutable.then_some(syn::Token![mut](span));
                let self_path = type_path!(span; Self);
                let (reference, mutability, ty) = if self.is_borrowed {
                    let and_token = syn::Token![&](span);
                    let ty = syn::TypeReference {
                        and_token,
                        lifetime: None,
                        mutability: mut_token,
                        elem: Box::new(self_path),
                    }
                    .into();

                    (Some((and_token, None)), None, ty)
                } else {
                    (None, mut_token, self_path)
                };

                syn::FnArg::Receiver(syn::Receiver {
                    attrs: vec![],
                    reference,
                    mutability,
                    self_token: syn::Token![self](span),
                    colon_token: None,
                    ty: Box::new(ty),
                })
            }
        }

        // This closure is a helper for constructing `syn::Signature`s.
        //
        // Note that the `inputs` argument does not include the receiver, which is specified
        // separately by the `receiver` argument.
        let make_sig_for_block = |is_const: bool,
                                  is_unsafe: bool,
                                  ident: &str,
                                  receiver: Option<Receiver>,
                                  inputs: fn(Span2) -> Vec<syn::PatType>,
                                  output: fn(Span2) -> Option<syn::Type>,
                                  block: &syn::Block| {
            let span = block.span();

            syn::Signature {
                constness: is_const.then_some(syn::Token![const](span)),
                asyncness: None,
                unsafety: is_unsafe.then_some(syn::Token![unsafe](span)),
                abi: None,
                fn_token: syn::Token![fn](span),
                ident: syn::Ident::new(ident, span),
                generics: Default::default(),
                paren_token: syn::token::Paren(span),
                inputs: receiver
                    .into_iter()
                    .map(|it| it.into_arg(span))
                    .chain(inputs(span).into_iter().map(syn::FnArg::Typed))
                    .collect(),
                variadic: None,
                output: match output(span) {
                    Some(ty) => syn::ReturnType::Type(syn::Token![->](span), Box::new(ty)),
                    None => syn::ReturnType::Default,
                },
            }
        };

        /// Constructs a [`syn::Signature`] and [`syn::Block`] pair.
        macro_rules! make_fn_from_block {
            (
                is_const: $is_const:expr,
                is_unsafe: $is_unsafe:expr,
                receiver: $receiver:expr,
                inputs: $inputs:expr,
                output: $output:expr,
                block: $block:ident $(,)?
            ) => {
                (
                    make_sig_for_block(
                        $is_const,
                        $is_unsafe,
                        stringify!($block),
                        $receiver,
                        $inputs,
                        $output,
                        &self.$block,
                    ),
                    self.$block,
                )
            };
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
            make_fn_from_block! {
                is_const: false,
                is_unsafe: true,
                receiver: None,
                inputs: |span| vec![make_repr_arg(span)],
                output: |span| Some(type_path!(span; Self)),
                block: from_repr_unchecked,
            },
            make_fn_from_block! {
                is_const: false,
                is_unsafe: false,
                receiver: None,
                inputs: |span| vec![make_repr_arg(span)],
                output: |span| Some(make_option_self_ty(span)),
                block: from_repr_checked,
            },
            make_fn_from_block! {
                is_const: false,
                is_unsafe: false,
                receiver: Some(Receiver { is_borrowed: true, is_mutable: false }),
                inputs: |_| vec![],
                output: |span| Some(type_path!(span; Self::Repr)),
                block: to_repr,
            },
            make_fn_from_block! {
                is_const: false,
                is_unsafe: false,
                receiver: Some(Receiver { is_borrowed: false, is_mutable: false }),
                inputs: |_| vec![],
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
