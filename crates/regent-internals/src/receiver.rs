// SPDX-License-Identifier: MPL-2.0

//! Models a receiver function argument: `self`, `mut self`, `&self`, or `&mut self`.

use super::*;

/// Models a receiver function argument: `self`, `mut self`, `&self`, or `&mut self`.
pub(crate) struct Receiver {
    /// Whether or not this receiver is borrowed.
    is_borrowed: bool,
    /// Whether or not this receiver is mutable.
    is_mutable: bool,
}

impl Receiver {
    /// Creates a `Receiver` of the form `self`.
    pub(crate) fn new_self() -> Self {
        Self { is_borrowed: false, is_mutable: false }
    }

    /// Creates a `Receiver` of the form `mut self`.
    pub(crate) fn new_mut_self() -> Self {
        Self { is_borrowed: false, is_mutable: true }
    }

    /// Creates a `Receiver` of the form `&self`.
    pub(crate) fn new_ref_self() -> Self {
        Self { is_borrowed: true, is_mutable: false }
    }

    /// Creates a `Receiver` of the form `&mut self`.
    pub(crate) fn new_ref_mut_self() -> Self {
        Self { is_borrowed: true, is_mutable: true }
    }

    /// Converts this into a [`syn::FnArg`] with the given span.
    pub(crate) fn into_arg(self, span: Span2) -> syn::FnArg {
        let mutability = self.is_mutable.then_some(syn::Token![mut](span));
        let self_path = ty_path!(span; Self);
        let (reference, ty) = if self.is_borrowed {
            let and_token = syn::Token![&](span);
            // Rendered:
            //   &#mutability Self
            let ty = syn::TypeReference {
                and_token,
                lifetime: None,
                mutability,
                elem: Box::new(self_path),
            }
            .into();

            (Some((and_token, None)), ty)
        } else {
            (None, self_path)
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
