// SPDX-License-Identifier: MPL-2.0

use crate::prelude::*;

/// Produces a [`syn::Expr`] of the form `<#ty as ::regent::Bitwise>::WIDTH`.
pub(crate) fn make_bitwise_width(span: Span2, ty: syn::Type) -> syn::Expr {
    syn::ExprPath {
        attrs: vec![],
        qself: Some(syn::QSelf {
            lt_token: syn::Token![<](span),
            ty: Box::new(ty),
            position: 2,
            as_token: Some(syn::Token![as](span)),
            gt_token: syn::Token![>](span),
        }),
        path: su::path::make_bitwise_tail(span, [su::ident::WIDTH_ITEM.make_ident(span)]),
    }
    .into()
}
