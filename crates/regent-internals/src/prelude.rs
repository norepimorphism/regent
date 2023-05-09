// SPDX-License-Identifier: MPL-2.0

//! Common items.

mod checks;
mod error;
mod sum;
pub(crate) mod uint;

pub(crate) use std::iter::once;

pub(crate) use checks::*;
pub(crate) use error::Error;
pub(crate) use proc_macro::TokenStream;
pub(crate) use proc_macro2::{Span as Span2, TokenStream as TokenStream2};
pub(crate) use sum::*;
pub(crate) use syn::{
    __private::ToTokens,
    parse::Parser as _,
    punctuated::Punctuated,
    spanned::Spanned as _,
};
