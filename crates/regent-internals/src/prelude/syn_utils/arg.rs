// SPDX-License-Identifier: MPL-2.0

use crate::prelude::*;

/// Produces a [`syn::FnArg`] of the form `repr: Self::Repr`.
pub(crate) fn make_self_repr(span: Span2) -> syn::FnArg {
    syn::FnArg::Typed(syn::PatType {
        attrs: vec![],
        pat: Box::new(
            syn::PatPath {
                attrs: vec![],
                qself: None,
                path: su::ident::REPR_LOCAL.make_ident(span).into(),
            }
            .into(),
        ),
        colon_token: syn::Token![:](span),
        ty: Box::new(su::ty::make_self_repr(span)),
    })
}
