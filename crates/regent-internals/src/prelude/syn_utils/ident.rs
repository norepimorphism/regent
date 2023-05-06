// SPDX-License-Identifier: MPL-2.0

use crate::prelude::*;

/// Generates a static [`Name`] item with the given identifier and inner value.
macro_rules! name {
    ($ident:ident : $inner:expr $(,)?) => {
        pub(crate) static $ident: Name = Name($inner);
    };
}

name!(BITWISE_ITEM: "Bitwise");
name!(REGENT: "regent");
name!(REPR_LOCAL: "repr");
name!(REPR_ITEM: "Repr");
name!(SELF_ITEM: "Self");
name!(WIDTH_ITEM: "WIDTH");

/// The name-part of an identifier.
pub(crate) struct Name(&'static str);

impl Name {
    /// Transforms this name into a [`syn::Ident`] with the given span.
    pub(crate) fn make_ident(&self, span: Span2) -> syn::Ident {
        syn::Ident::new(self.0, span)
    }

    /// Transforms this name into a [`syn::PathSegment`] with the given span.
    pub(crate) fn make_path_segment(&self, span: Span2) -> syn::PathSegment {
        self.make_ident(span).into()
    }
}
