// SPDX-License-Identifier: MPL-2.0

//! Utilities and helpers for the [`syn`] crate.

use super::*;

/// Constructs a type of the form `Self`.
pub(crate) fn make_self_ty(span: Span2) -> syn::Type {
    syn::TypePath { qself: None, path: syn::Ident::new("Self", span).into() }.into()
}

/// Constructs a type of the form `::core::option::Option::<Self>`.
pub(crate) fn make_option_self_ty(span: Span2) -> syn::Type {
    let segments = ["core", "option"]
        .into_iter()
        .map(|it| syn::Ident::new(it, span).into())
        .chain(once(syn::PathSegment {
            ident: syn::Ident::new("Option", span),
            arguments: syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
                colon2_token: Some(syn::Token![::](span)),
                lt_token: syn::Token![<](span),
                args: once(syn::GenericArgument::Type(
                    syn::TypePath { qself: None, path: syn::Ident::new("Self", span).into() }
                        .into(),
                ))
                .collect(),
                gt_token: syn::Token![>](span),
            }),
        }))
        .collect();

    syn::TypePath {
        qself: None,
        path: syn::Path { leading_colon: Some(syn::Token![::](span)), segments },
    }
    .into()
}

/// Constructs a type of the form `Self::Repr`.
pub(crate) fn make_self_repr_ty(span: Span2) -> syn::Type {
    syn::TypePath {
        qself: None,
        path: syn::Path {
            leading_colon: None,
            segments: ["Self", "Repr"]
                .into_iter()
                .map(|it| syn::PathSegment::from(syn::Ident::new(it, span)))
                .collect(),
        },
    }
    .into()
}

/// Constructs a function argument of the form `repr: Self::Repr`.
pub(crate) fn make_self_repr_arg(span: Span2) -> syn::FnArg {
    syn::FnArg::Typed(syn::PatType {
        attrs: vec![],
        pat: Box::new(
            syn::PatPath { attrs: vec![], qself: None, path: syn::Ident::new("repr", span).into() }
                .into(),
        ),
        colon_token: syn::Token![:](span),
        ty: Box::new(make_self_repr_ty(span)),
    })
}
