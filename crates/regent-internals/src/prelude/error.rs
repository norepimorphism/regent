// SPDX-License-Identifier: MPL-2.0

//! The error type returned by fallible functions in *regent-internals*.

use super::*;

/// The error type returned by fallible functions in *regent-internals*.
///
/// This is a wrapper over [`syn::Error`] and is convertible into `syn::Error` and token streams.
pub(crate) struct Error(syn::Error);

impl Error {
    /// Wraps a [`syn::Error`].
    pub(crate) fn new(e: syn::Error) -> Self {
        Self(e)
    }
}

impl From<Error> for syn::Error {
    fn from(e: Error) -> Self {
        e.0
    }
}

impl From<Error> for TokenStream {
    fn from(e: Error) -> Self {
        TokenStream2::from(e).into()
    }
}

impl From<Error> for TokenStream2 {
    fn from(e: Error) -> Self {
        e.0.into_compile_error()
    }
}
