// SPDX-License-Identifier: MPL-2.0

//! Models of unsigned integer types.

use std::fmt;

use super::*;

/// Models an unsigned integer type of arbitrary bit-width: <code>u&#8239;<em>width</em></code>.
///
/// This type is not [spanned](Span2).
pub(crate) struct PseudoType {
    width: usize,
}

impl PseudoType {
    /// Attempts to parse a `PseudoType` from a [`syn::Ident`].
    ///
    /// This returns `None` if `ident` is not an unsigned integer (i.e., not of the form
    /// <code>u&#8239;<em>width</em></code>), `Some(Err(_))` if `ident` appears to be an unsigned
    /// integer but the *width* suffix fails to parse or is zero, and `Some(Ok(_))` otherwise.
    pub(crate) fn parse(ident: syn::Ident) -> Option<Result<Self, Error>> {
        let (span, ident) = (ident.span(), ident.to_string());
        let Some(("", width)) = ident.split_once('u') else {
            // This is not even an unsigned integer.
            return None;
        };
        let Ok(width) = width.parse() else {
            // FIXME: improve error message
            return Some(Err(err!(span; "failed to parse integer width suffix")));
        };
        if width == 0 {
            return Some(Err(err!(span; "this cannot be zero-sized")));
        }

        Some(Ok(Self { width }))
    }

    /// The bit-width of this type.
    pub(crate) fn width(&self) -> usize {
        self.width
    }

    /// Rounds [the width] of this type up to the next smallest power of two that is at least 8.
    ///
    /// [the width]: Self::width
    ///
    /// This type is not guaranteed to [exist] after calling this method. For example, if the
    /// original width was 255, it will be rounded up to 256 despite the nonexistence of the `u256`
    /// primitive.
    ///
    /// [exist]: Self::exists
    fn round_up(&mut self) {
        if self.width <= 8 {
            self.width = 8;
            return;
        }

        // This is the integer component (magnitude) of `log2(width)`.
        let mag = self.width.ilog2() as usize;
        // This is the fractional component (remainder) of `log2(width)`.
        let rem = self.width & ((1 << mag) - 1);

        if rem > 0 {
            self.width = 1 << (mag + 1);
        }
    }

    /// Determines if this pseudo-type models an unsigned integer primitive that exists in Rust.
    ///
    /// This method returns `true` only if [the width] of this type is a power of two between 8 and
    /// 128, inclusive.
    ///
    /// [the width]: Self::width
    pub(crate) fn exists(&self) -> bool {
        match self.width {
            8 | 16 | 32 | 64 | 128 => true,
            _ => false,
        }
    }

    /// Attempts to convert this `PseudoType` into a [`RustType`].
    ///
    /// This method returns `None` if this pseudo-type does not [exist].
    ///
    /// [exist]: Self::exists
    pub(crate) fn try_into_rust_type(self) -> Option<RustType> {
        self.exists().then(|| RustType { width: self.width })
    }
}

/// Models an unsigned integer primitive that exists in Rust: `u8`, `u16`, `u32`, `u64`, or `u128`.
///
/// This type is not [spanned](Span2).
pub(crate) struct RustType {
    width: usize,
}

impl RustType {
    /// Determines the best representation for an item.
    ///
    /// ### Arguments
    ///
    /// `expected_width` may contain a bit-width originating from the [`size`] or [`width`]
    /// arguments to the `#[bitwise]` attribute. If present, this bit-width represents the user's
    /// expectation of the minimum number of bits necessary to represent all struct fields or encode
    /// all enum variants&mdash;whichever it is.
    ///
    /// [`size`]: crate::Args::size
    /// [`width`]: crate::Args::width
    ///
    /// `item_width` is the actual computed bit-width of the item. This method makes no assumption
    /// as to whether this value is equivalent to `expected_width`.
    ///
    /// `item_attrs` is a mutable reference to the list of outer attributes on the item.
    ///
    /// ### Behavior
    ///
    /// If `item_attrs` contains a `#[repr]` attribute, its argument is parsed as a [`PseudoType`].
    /// If successful, the attribute is removed from `item_attrs` (so it will not appear on the
    /// emitted item), and then the `PseudoType` is converted to `RustType` and returned as the
    /// item's representation. Otherwise, an error is returned.
    ///
    /// If `item_attrs` does not contain a `#[repr]` attribute, the `expected_width` and
    /// `item_width` arguments are consulted, in that order, as candidates for the bit-width of the
    /// item's representation. If `expected_width` is `Some(_)`, its corresponding `PseudoType` is
    /// rounded up to a `RustType` and returned. Otherwise, if `item_width` is determinate at
    /// macro evaluation time (i.e., of kind [`Met`]), its `PseudoType` is rounded up and returned.
    /// Finally, if neither candidate succeeds, an error is returned.
    ///
    /// [`Met`]: Width::Met
    pub(crate) fn repr_for_item(
        expected_width: Option<usize>,
        item_width: &Width,
        item_attrs: &mut Vec<syn::Attribute>,
    ) -> Result<Self, Error> {
        if let Some((i, attr)) =
            item_attrs.iter().enumerate().find(|(_, attr)| attr.path().is_ident("repr"))
        {
            let repr = attr.parse_args::<syn::Ident>().map_err(Error::new).and_then(|ident| {
                let span = ident.span();

                match PseudoType::parse(ident) {
                    Some(Ok(ty)) => ty.try_into_rust_type().ok_or_else(|| err!(
                        span;
                        "argument cannot be a pseudo-type",
                    )),
                    Some(Err(e)) => Err(e),
                    None => Err(err!(span; "argument must be an unsigned integer primitive")),
                }
            })?;
            item_attrs.remove(i);

            Ok(repr)
        } else {
            let span = expected_width.span();

            let mut pseudo = if let Some(width) = expected_width {
                PseudoType { width }
            } else {
                match item_width {
                    Width::Met(_, width) => PseudoType { width: *width },
                    Width::Ct(_) => {
                        return Err(err!(
                            span;
                            "not enough information to compute item width at macro evaluation time",
                        ));
                    }
                }
            };
            pseudo.round_up();

            pseudo.try_into_rust_type().ok_or_else(|| err!(
                span;
                "item cannot be represented by any unsigned integer primitive",
            ))
        }
    }

    /// The bit-width of this type.
    pub(crate) fn width(&self) -> usize {
        self.width
    }

    /// Converts this `RustType` into a [`syn::Type`].
    pub(crate) fn into_syn_type(self, span: Span2) -> syn::Type {
        syn::TypePath {
            qself: None,
            path: syn::Ident::new(&self.to_string(), span).into(),
        }
        .into()
    }
}

impl fmt::Display for RustType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "u{}", self.width)
    }
}
