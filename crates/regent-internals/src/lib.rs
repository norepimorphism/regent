// SPDX-License-Identifier: MPL-2.0

//! Procedural macro implementations for [Regent](https://crates.io/crates/regent).
//!
//! This crate provides the [`bitwise`] proc macro that is re-exported by the main *regent* crate.

/// Like [`try`](std::try) except the return type of the containing function is `T` instead of
/// [`Result<T, E>`](Result).
macro_rules! unwrap {
    ($expr:expr) => {
        match $expr {
            Ok(it) => it,
            Err(e) => { return e; }
        }
    };
}

/// Creates an [`Error`] with the given message and, optionally, span.
///
/// If no span is specified, [`call_site`](Span2::call_site) is used.
macro_rules! err {
    ($fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        err!(Span2::call_site();  $fmt $(, $fmt_arg)*)
    };
    ($span:expr ; $fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        Error::new(syn::Error::new($span, format!($fmt $(, $fmt_arg)*)))
    };
}

/// Creates a [`syn::Path`] from the given path segments and span.
macro_rules! path {
    ($span:expr ; $($seg:tt)*) => {
        path!(@internal => {
            span: $span,
            leading_colon: None,
            segments: $($seg)*
        })
    };
    ($span:expr ; :: $($seg:tt)*) => {
        path!(@internal => {
            span: $span,
            leading_colon: Some(syn::Token![::]($span)),
            segments: $($seg)*
        })
    };
    (@internal => {
        span: $span:expr,
        leading_colon: $leading_colon:expr,
        segments: $($seg:tt)*
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

/// Creates a [`syn::TypePath`] from the given path segments and span.
macro_rules! type_path {
    ($span:expr ; $($path_piece:tt)*) => {
        syn::TypePath { qself: None, path: path!($span; $($path_piece)*) }.into()
    };
}

mod r#enum;
mod prelude;
mod r#struct;

use r#enum::Enum;
use prelude::*;
use r#struct::Struct;

/// The whole point.
///
/// Refer to the `spec` module in the crate root for usage information.
#[proc_macro_attribute]
pub fn bitwise(args: TokenStream, item: TokenStream) -> TokenStream {
    let args = unwrap!(Args::parse(args).map_err(TokenStream::from));
    let expected_width = args.expected_width();

    let result = match syn::parse_macro_input!(item as _) {
        syn::Item::Struct(item) => Struct::bitwise(expected_width, item).map(TokenStream::from),
        syn::Item::Enum(item) => Enum::bitwise(expected_width, item).map(TokenStream::from),
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
        syn::meta::parser(|meta| {
            let ident = meta.path.get_ident().ok_or_else(|| -> syn::Error {
                err!(meta.path.span(); "argument path must be an identifier").into()
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
        .map_err(Error::new)?;

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
    ///
    /// # Arguments
    ///
    /// `expected_width` is the result of [`Args::expected_width`]. `item` is the primary input to
    /// the macro.
    fn bitwise(expected_width: Option<usize>, item: Self::Item) -> Result<Output<Self::Item>, Error>;
}

/// The output of [`Form::bitwise`].
struct Output<Item> {
    /// An optional [block](syn::Block) to be executed in a `const` context at the global scope.
    ///
    /// When present, this block typically contains compile-time assertions for invariants that
    /// cannot be checked at macro evaluation time.
    const_block: Option<syn::Block>,
    /// The emitted item.
    item: Item,
    /// The <code>impl&nbsp;<em>item</em></code> [impl block](syn::ItemImpl) for [the emitted
    /// item](Self::item).
    impl_item: Option<syn::ItemImpl>,
    /// The implementation of the `Bitwise` trait for [the emitted item](Self::item).
    impl_bitwise_for_item: BitwiseImpl,
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
}

impl<Item: ToTokens> From<Output<Item>> for TokenStream {
    fn from(output: Output<Item>) -> Self {
        TokenStream2::from(output).into()
    }
}

impl<Item: ToTokens> From<Output<Item>> for TokenStream2 {
    fn from(output: Output<Item>) -> Self {
        macro_rules! make_token_streams {
            ($($to_tokens:expr),* $(,)?) => { [$($to_tokens.into_token_stream()),*] };
        }

        let item_span = output.item.span();

        make_token_streams![
            output.const_block.map(Output::<Item>::make_const_item),
            output.item,
            output.impl_item,
            output.impl_bitwise_for_item.into_item_impl(item_span),
        ]
        .into_iter()
        .collect()
    }
}

impl<Item> Output<Item> {
    fn make_const_item(block: syn::Block) -> syn::ItemConst {
        let span = block.span();

        syn::ItemConst {
            attrs: vec![],
            vis: syn::Visibility::Inherited,
            const_token: syn::Token![const](span),
            ident: syn::Ident::new("_", span),
            generics: Default::default(),
            colon_token: syn::Token![:](span),
            ty: Box::new(syn::TypeTuple {
                paren_token: syn::token::Paren(span),
                elems: Punctuated::new(),
            }.into()),
            eq_token: syn::Token![=](span),
            expr: Box::new(syn::ExprBlock { attrs: vec![], label: None, block }.into()),
            semi_token: syn::Token![;](span),
        }
    }
}

impl BitwiseImpl {
    fn into_item_impl(self, span: Span2) -> syn::ItemImpl {
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

        let width_item = syn::ImplItemConst {
            attrs: vec![],
            vis: syn::Visibility::Inherited,
            defaultness: None,
            const_token,
            ident: syn::Ident::new("WIDTH", span),
            generics: Default::default(),
            colon_token,
            ty: syn::TypePath { qself: None, path: path!(span; usize) }.into(),
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
            self_ty: Box::new(syn::TypePath { qself: None, path: self.ident.into() }.into()),
            brace_token,
            items,
        }
    }
}

impl BitwiseFuncs {
    /// Converts this into an iterator of [`syn::ImplItemFn`]s.
    fn into_iter(self) -> impl Iterator<Item = syn::ImplItemFn> {
        struct Receiver {
            is_borrowed: bool,
            is_mutable: bool,
        }

        impl Receiver {
            fn into_arg(self, span: Span2) -> syn::FnArg {
                syn::FnArg::Receiver(syn::Receiver {
                    attrs: vec![],
                    reference: self.is_borrowed.then_some((syn::Token![&](span), None)),
                    mutability: self.is_mutable.then_some(syn::Token![mut](span)),
                    self_token: syn::Token![self](span),
                    colon_token: None,
                    ty: Box::new(type_path!(span; Self)),
                })
            }
        }

        let make_sig_for_block = |is_const: bool,
                                  is_unsafe: bool,
                                  ident: &str,
                                  receiver: Option<Receiver>,
                                  inputs: fn(Span2) -> Vec<syn::FnArg>,
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
                    .chain(inputs(span))
                    .collect(),
                variadic: None,
                output: match output(span) {
                    Some(ty) => syn::ReturnType::Type(syn::Token![->](span), Box::new(ty)),
                    None => syn::ReturnType::Default,
                },
            }
        };

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

        fn make_repr_arg(span: Span2) -> syn::FnArg {
            syn::FnArg::Typed(syn::PatType {
                attrs: vec![],
                pat: Box::new(
                    syn::PatPath {
                        attrs: vec![],
                        qself: None,
                        path: path!(span; repr),
                    }
                    .into(),
                ),
                colon_token: syn::Token![:](span),
                ty: Box::new(type_path!(span; Self::Repr)),
            })
        }

        fn make_option_self_ty(span: Span2) -> syn::Type {
            let segments = ["core", "option"]
                .into_iter()
                .map(|it| syn::Ident::new(it, span).into())
                .chain([syn::PathSegment {
                    ident: syn::Ident::new("Option", span),
                    arguments: syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
                        colon2_token: Some(syn::Token![::](span)),
                        lt_token: syn::Token![<](span),
                        args: once(syn::GenericArgument::Type(type_path!(span; Self))).collect(),
                        gt_token: syn::Token![>](span),
                    }),
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
                receiver: Some(Receiver { is_borrowed: false, is_mutable: false }),
                inputs: |_| vec![],
                output: |span| Some(type_path!(span; Self::Repr)),
                block: to_repr,
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
