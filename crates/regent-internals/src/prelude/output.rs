// SPDX-License-Identifier: MPL-2.0

//! The output of the `bitwise` macro.

use super::*;

/// The output of the `bitwise` macro.
pub(crate) struct Output {
    /// The emitted item.
    pub(crate) item: syn::Item,
    /// The `impl #item` block.
    pub(crate) item_impl: syn::ItemImpl,
    /// The `impl Bitwise for #item` block.
    pub(crate) bitwise_impl: BitwiseImpl,
}

/// An implementation of the `Bitwise` trait.
pub(crate) struct BitwiseImpl {
    /// The type identifier of the implementor.
    pub(crate) ident: syn::Ident,
    /// The bit-width of the implementor.
    pub(crate) width: Width,
    /// The internal representation, or backing storage, of the implementor.
    pub(crate) repr: UIntType,
    /// The associated function implementations.
    pub(crate) funcs: BitwiseFuncs,
}

/// Associated function implementations for the `Bitwise` trait.
///
/// This struct consists of [`syn::Block`]s rather than [`syn::ItemFn`]s because the function
/// signatures can be inferred from context.
pub(crate) struct BitwiseFuncs {
    /// The block for the `from_repr_unchecked` function.
    pub(crate) from_repr_unchecked: syn::Block,
    /// The block for the `from_repr_checked` function.
    pub(crate) from_repr_checked: syn::Block,
    /// The block for the `to_repr` function.
    pub(crate) to_repr: syn::Block,
}

impl From<Output> for proc_macro::TokenStream {
    fn from(output: Output) -> Self {
        proc_macro2::TokenStream::from(output).into()
    }
}

impl From<Output> for proc_macro2::TokenStream {
    fn from(output: Output) -> Self {
        let item_span = output.item.span();

        [
            output.item.into_token_stream(),
            output.item_impl.into_token_stream(),
            output.bitwise_impl.into_item_impl(item_span).into_token_stream(),
        ]
        .into_iter()
        .collect()
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
            ident: su::ident::WIDTH_ITEM.make_ident(span),
            generics: Default::default(),
            colon_token,
            ty: syn::TypePath { qself: None, path: syn::Ident::new("usize", span).into() }.into(),
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
            ident: su::ident::REPR_ITEM.make_ident(span),
            generics: Default::default(),
            eq_token,
            ty: syn::TypePath { qself: None, path: self.repr.make_ident(span).into() }.into(),
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
            trait_: Some((None, su::path::make_bitwise(span), for_token)),
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
                    ty: Box::new(su::ty::make_self(span)),
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

        [
            make_fn_from_block! {
                is_const: false,
                is_unsafe: true,
                receiver: None,
                inputs: |span| vec![su::arg::make_self_repr(span)],
                output: |span| Some(su::ty::make_self(span)),
                block: from_repr_unchecked,
            },
            make_fn_from_block! {
                is_const: false,
                is_unsafe: false,
                receiver: None,
                inputs: |span| vec![su::arg::make_self_repr(span)],
                output: |span| Some(su::ty::make_option_self(span)),
                block: from_repr_checked,
            },
            make_fn_from_block! {
                is_const: false,
                is_unsafe: false,
                receiver: Some(Receiver { is_borrowed: false, is_mutable: false }),
                inputs: |_| vec![],
                output: |span| Some(su::ty::make_self_repr(span)),
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
