// SPDX-License-Identifier: MPL-2.0

use crate::prelude::*;

/// Produces a [`syn::Type`] of the form `Self`.
pub(crate) fn make_self(span: Span2) -> syn::Type {
    make_self_tail::<syn::PathSegment>(span, [])
}

/// Produces a [`syn::Type`] of the form `Self::Repr`.
pub(crate) fn make_self_repr(span: Span2) -> syn::Type {
    make_self_tail(span, [su::ident::REPR_ITEM.make_path_segment(span)])
}

/// Produces a [`syn::Type`] of the form `Self::#tail`.
pub(crate) fn make_self_tail<S>(span: Span2, tail: impl IntoIterator<Item = S>) -> syn::Type
where
    S: Into<syn::PathSegment>,
{
    let segments = once(su::ident::SELF_ITEM.make_path_segment(span))
        .chain(tail.into_iter().map(S::into))
        .collect();

    syn::TypePath { qself: None, path: syn::Path { leading_colon: None, segments } }.into()
}

/// Produces a [`syn::Type`] of the form `::core::option::Option::<Self>`.
pub(crate) fn make_option_self(span: Span2) -> syn::Type {
    let segments = ["core", "option"]
        .into_iter()
        .map(|it| syn::Ident::new(it, span).into())
        .chain([syn::PathSegment {
            ident: syn::Ident::new("Option", span),
            arguments: syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
                colon2_token: Some(syn::Token![::](span)),
                lt_token: syn::Token![<](span),
                args: once(syn::GenericArgument::Type(make_self(span))).collect(),
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
