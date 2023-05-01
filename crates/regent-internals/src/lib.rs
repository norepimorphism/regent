// SPDX-License-Identifier: MPL-2.0

//! Procedural macro implementations for [Regent].
//!
//! This crate, *regent-internals*, provides the [`bitwise`] proc macro that is re-exported by the
//! main *regent* crate. The purpose and usage of `bitwise` are described in [the README there]. Any
//! documentation-related issues should be reported to [the GitHub repository]. (Thanks!)
//!
//! [Regent]: https://crates.io/crates/regent
//! [the README there]: https://crates.io/crates/regent#regent
//! [the GitHub repository]: https://github.com/norepimorphism/regent

/// Like [`try`](std::try) except the return type of the containing function is `T` instead of
/// [`Result<T, E>`](std::result::Result).
macro_rules! unwrap {
    ($expr:expr) => {
        match $expr {
            Ok(it) => it,
            Err(e) => {
                return e;
            }
        }
    };
}

/// Creates an [`Error`] with the given message and, optionally, span.
///
/// If no span is specified, [`call_site`](Span2::call_site) is used.
macro_rules! err {
    ($fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        err!(Span2::call_site();  $fmt $(, $fmt_arg)*)
    };
    ($span:expr ; $fmt:expr $(, $fmt_arg:expr)* $(,)?) => {
        Error::new(syn::Error::new($span, format!($fmt $(, $fmt_arg)*)))
    };
}

mod on_enum;
mod on_struct;
mod prelude;

use prelude::*;

/// Does the thing.
#[proc_macro_attribute]
pub fn bitwise(args: TokenStream, item: TokenStream) -> TokenStream {
    let args = unwrap!(Args::parse(args).map_err(TokenStream::from));
    let expected_width = args.expected_width();

    let result = match syn::parse_macro_input!(item as _) {
        syn::Item::Enum(item) => on_enum::bitwise(expected_width, item),
        syn::Item::Struct(item) => on_struct::bitwise(expected_width, item),
        item => Err(err!(item.span(); "item must be a struct or enum").into()),
    };

    match result {
        Ok(it) => it.into(),
        Err(e) => e.into(),
    }
}

///// PRIVATE API //////////////////////////////////////////////////////////////////////////////////

/// Acceptable arguments to the `bitwise` attribute.
#[derive(Default)]
struct Args {
    /// The 'size' argument, if any.
    ///
    /// This determines the size, in bytes, of the emitted item. This argument is
    /// mutually-exclusive with the 'width' argument.
    size: Option<usize>,
    /// The 'width' argument, if any.
    ///
    /// This determines the width, in bits, of the emitted item. This argument is
    /// mutually-exclusive with the 'size' argument.
    width: Option<usize>,
}

impl Args {
    /// Parses comma-separated attribute arguments from the given [`TokenStream`].
    fn parse(args: TokenStream) -> Result<Self, Error> {
        let mut result = Self::default();
        syn::meta::parser(|meta| {
            let ident = meta.path.get_ident().ok_or_else(|| -> syn::Error {
                err!(meta.path.span(); "attribute argument must be an identifier").into()
            })?;
            let arg = if ident == "size" {
                &mut result.size
            } else if ident == "width" {
                &mut result.width
            } else {
                return Err(err!(ident.span(); "attribute argument is not supported").into());
            };
            if arg.is_some() {
                return Err(err!(meta.path.span(); "attribute argument is a duplicate").into());
            }
            let value = meta
                .value()
                .and_then(|it| it.parse::<syn::LitInt>())
                .and_then(|it| it.base10_parse())?;
            *arg = Some(value);

            Ok(())
        })
        .parse(args)
        .map_err(Error::new)?;

        if result.size.is_some() && result.width.is_some() {
            return Err(err!("`size` and `width` attribute arguments are mutually exclusive"));
        }

        Ok(result)
    }

    /// The expected bit-width, if any, of the emitted item.
    fn expected_width(&self) -> Option<usize> {
        self.width.or_else(|| self.size.map(|it| it * 8))
    }
}
