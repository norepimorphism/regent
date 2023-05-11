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
            return Some(Err(err!(span; "integer has invalid width suffix")));
        };
        if width == 0 {
            return Some(Err(err!(span; "this cannot be zero-sized")));
        }

        Some(Ok(Self { width }))
    }

    /// The bit-width of this type.
    #[allow(unused)]
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
    /// This method returns `None` if this pseudo-type does not [exist](Self::exists).
    pub(crate) fn try_into_rust_type(self) -> Option<RustType> {
        self.exists().then(|| RustType { width: self.width })
    }
}

/// Models an unsigned integer primitive that exists in Rust: `u8`, `u16`, `u32`, `u64`, or `u128`.
///
/// This type is not [spanned](Span2).
#[derive(Clone, Copy)]
pub(crate) struct RustType {
    width: usize,
}

impl RustType {
    /// Determines the best representation for an item.
    ///
    /// If `item_attrs` contains a `#[repr]` attribute, its argument is parsed as a [`PseudoType`].
    /// If successful, the attribute is removed from `item_attrs` (so it will not appear on the
    /// emitted item), and then the `PseudoType` is converted to `RustType` and returned.
    ///
    /// If `item_attrs` does not contain a `#[repr]` attribute but the `item_width` argument is
    /// determinate at macro evaluation time (i.e., of kind [`Met`]), a `PseudoType` is constructed
    /// with width `item_width`, [rounded up] to a `RustType`, and returned.
    ///
    /// If neither of these conditions are satisfied, an error is returned.
    ///
    /// [`Met`]: Width::Met
    /// [rounded up]: PseudoType::round_up
    ///
    /// # Arguments
    ///
    /// `item_span` is a span covering the entire item. `item_width` is the computed bit-width of
    /// the item. `item_attrs` is a mutable reference to the list of outer attributes on the item.
    pub(crate) fn repr_for_item(
        item_span: Span2,
        item_width: &Width,
        item_attrs: &mut Vec<syn::Attribute>,
    ) -> Result<Self, Error> {
        if let Some((i, attr)) =
            item_attrs.iter().enumerate().find(|(_, attr)| attr.path().is_ident("repr"))
        {
            let ident = attr.parse_args::<syn::Ident>().map_err(Error)?;
            let span = ident.span();
            let repr = match PseudoType::parse(ident) {
                Some(Ok(ty)) => ty
                    .try_into_rust_type()
                    .ok_or_else(|| err!(span; "argument cannot be a pseudo-type")),
                Some(Err(e)) => Err(e),
                None => Err(err!(span; "argument must be an unsigned integer primitive")),
            }?;
            item_attrs.remove(i);

            return Ok(repr);
        }

        let mut pseudo_type = match item_width {
            Width::Met(_, width) => PseudoType { width: *width },
            Width::Ct(_) => {
                return Err(err!(
                    item_span;
                    "not enough information to compute item width at macro evaluation time",
                ));
            }
        };
        pseudo_type.round_up();

        pseudo_type.try_into_rust_type().ok_or_else(|| {
            err!(
                item_span;
                "item cannot be represented by any unsigned integer primitive",
            )
        })
    }

    /// The bit-width of this type.
    #[allow(unused)]
    pub(crate) fn width(&self) -> usize {
        self.width
    }

    /// Converts this `RustType` into a [`syn::Type`].
    pub(crate) fn into_syn_type(self, span: Span2) -> syn::Type {
        type_path!(syn::Ident::new(&self.to_string(), span))
    }
}

impl fmt::Display for RustType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "u{}", self.width)
    }
}
