// SPDX-License-Identifier: MPL-2.0

//! Procedural macro implementations for [Regent].
//!
//! This crate provides the [`bitwise`] proc macro that is re-exported by the main *regent* crate.
//! The purpose and usage of `bitwise` are described in [the README there]. Any
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

mod r#enum;
mod prelude;
mod r#struct;

use prelude::*;

/// Does the thing.
#[proc_macro_attribute]
pub fn bitwise(args: TokenStream, item: TokenStream) -> TokenStream {
    let args = unwrap!(Args::parse(args).map_err(TokenStream::from));
    let expected_width = args.expected_width();

    let result = match syn::parse_macro_input!(item as _) {
        syn::Item::Struct(item) => r#struct::bitwise(expected_width, item),
        syn::Item::Enum(item) => r#enum::bitwise(expected_width, item),
        item => Err(err!(item.span(); "item must be a struct or enum").into()),
    };

    match result {
        Ok(it) => it.into(),
        Err(e) => e.into(),
    }
}

/// Acceptable arguments to the `#[bitwise]` attribute.
#[derive(Default)]
struct Args {
    /// The 'size' argument, if any.
    ///
    /// This determines the size, in bytes, of the emitted item. This argument is
    /// mutually-exclusive with the '[width]' argument.
    ///
    /// [width]: Self::width
    size: Option<usize>,
    /// The 'width' argument, if any.
    ///
    /// This determines the width, in bits, of the emitted item. This argument is
    /// mutually-exclusive with the '[size]' argument.
    ///
    /// [size]: Self::size
    width: Option<usize>,
}

impl Args {
    /// Parses comma-separated arguments to the `#[bitwise]` attribute from the given
    /// [`TokenStream`].
    fn parse(args: TokenStream) -> Result<Self, Error> {
        let mut output = Self::default();
        syn::meta::parser(|meta| {
            let ident = meta.path.get_ident().ok_or_else(|| -> syn::Error {
                err!(meta.path.span(); "argument path must be an identifier").into()
            })?;
            let arg = if ident == "size" {
                &mut output.size
            } else if ident == "width" {
                &mut output.width
            } else {
                return Err(meta.error("argument is not supported"));
            };
            if arg.is_some() {
                return Err(meta.error("argument is a duplicate"));
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

        if output.size.is_some() && output.width.is_some() {
            return Err(err!("`size` and `width` arguments are mutually exclusive"));
        }

        Ok(output)
    }

    /// The expected bit-width, if any, of the emitted item.
    fn expected_width(&self) -> Option<usize> {
        self.width.or_else(|| self.size.map(|it| it * 8))
    }
}
