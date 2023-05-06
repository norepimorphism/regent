// SPDX-License-Identifier: MPL-2.0

//! Common items for internal use in *regent-internals*.

mod checks;
mod error;
mod output;
mod sum;
pub(crate) mod syn_utils;
mod ty;

pub(crate) use std::iter::once;

pub(crate) use checks::*;
pub(crate) use error::Error;
pub(crate) use output::Output;
pub(crate) use proc_macro::TokenStream;
pub(crate) use proc_macro2::{Span as Span2, TokenStream as TokenStream2};
pub(crate) use sum::{Sum, Width};
pub(crate) use syn::{
    __private::ToTokens,
    parse::Parser as _,
    punctuated::Punctuated,
    spanned::Spanned as _,
};
pub(crate) use syn_utils as su;
pub(crate) use ty::*;
