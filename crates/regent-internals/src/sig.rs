// SPDX-License-Identifier: MPL-2.0

//! A convenience builder for [`syn::Signature`]s.

use super::*;

/// A convenience builder for [`syn::Signature`]s.
pub(crate) struct Builder {
    is_const: bool,
    is_unsafe: bool,
    receiver: Option<Receiver>,
}

impl Builder {
    /// Creates a new `Builder`.
    ///
    /// At creation, the builder state models a non-`const`, non-`unsafe` function signature.
    pub(crate) fn new() -> Self {
        Self { is_const: false, is_unsafe: false, receiver: None }
    }

    /// Adds the `const` qualifier to the function signature.
    pub(crate) fn with_const(mut self) -> Self {
        self.is_const = true;

        self
    }

    /// Adds the `unsafe` qualifier to the function signature.
    pub(crate) fn with_unsafe(mut self) -> Self {
        self.is_unsafe = true;

        self
    }

    /// Adds a [receiver] argument to the function signature.
    ///
    /// [receiver]: Receiver
    pub(crate) fn with_receiver(mut self, receiver: Receiver) -> Self {
        self.receiver = Some(receiver);

        self
    }

    /// Consumes this builder to produce a [`syn::Signature`].
    ///
    /// # Arguments
    ///
    /// `span` is the [span] used for keywords (`const`, `unsafe`, `fn`) and the 'right arrow' token
    /// `->`. `ident` is the [identifier] corresponding to the name of the function. `get_inputs`
    /// and `get_output` are functions that receive the `span` argument by-copy and produce the
    /// function arguments and return type, respectively, for the resultant signature.
    ///
    /// [span]: Span2
    /// [identifier]: syn::Ident
    pub(crate) fn build<In>(
        self,
        span: Span2,
        ident: syn::Ident,
        get_inputs: impl FnOnce(Span2) -> In,
        get_output: impl FnOnce(Span2) -> Option<syn::Type>,
    ) -> syn::Signature
    where
        In: IntoIterator<Item = syn::PatType>,
    {
        let inputs = self
            .receiver
            .into_iter()
            .map(|it| it.into_arg(span))
            .chain(get_inputs(span).into_iter().map(syn::FnArg::Typed))
            .collect();
        let output = match get_output(span) {
            Some(ty) => syn::ReturnType::Type(syn::Token![->](span), Box::new(ty)),
            None => syn::ReturnType::Default,
        };

        syn::Signature {
            constness: self.is_const.then_some(syn::Token![const](span)),
            asyncness: None,
            unsafety: self.is_unsafe.then_some(syn::Token![unsafe](span)),
            abi: None,
            fn_token: syn::Token![fn](span),
            ident,
            generics: Default::default(),
            paren_token: syn::token::Paren(span),
            inputs,
            variadic: None,
            output,
        }
    }
}
