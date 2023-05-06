// SPDX-License-Identifier: MPL-2.0

use crate::prelude::*;

/// Produces a [`syn::Path`] of the form `::regent::Bitwise`.
pub(crate) fn make_bitwise(span: Span2) -> syn::Path {
    make_bitwise_tail::<syn::PathSegment>(span, [])
}

/// Produces a [`syn::Path`] of the form `::regent::Bitwise::#tail`.
pub(crate) fn make_bitwise_tail<S>(span: Span2, tail: impl IntoIterator<Item = S>) -> syn::Path
where
    S: Into<syn::PathSegment>,
{
    syn::Path {
        leading_colon: Some(syn::Token![::](span)),
        segments: [su::ident::REGENT, su::ident::BITWISE_ITEM]
            .into_iter()
            .map(|it| it.make_path_segment(span))
            .chain(tail.into_iter().map(S::into))
            .collect(),
    }
}
