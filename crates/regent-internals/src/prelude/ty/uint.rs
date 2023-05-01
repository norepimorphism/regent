// SPDX-License-Identifier: MPL-2.0

use super::*;

/// The internal representation, or backing storage, of an item emitted by *bitwise*.
pub(crate) type Repr = UIntType;

/// An unsigned integer type recognized by *bitwise*.
#[derive(Clone, Copy)]
pub(crate) struct UIntType {
    width: usize,
}

impl UIntType {
    /// The bit-width of this type.
    pub(crate) fn width(self) -> usize {
        self.width
    }

    /// Attempts to parse a `UIntType` from the given string.
    ///
    /// This returns `None` if `ty` is not an unsigned integer (i.e., of the form
    /// <code>u&nbsp;<em>width</em></code>), `Some(Err(_))` if `ty` *is* an
    /// unsigned integer but the width suffix fails to parse or is zero, and `Some(Ok(_))`
    /// otherwise.
    pub(crate) fn parse(span: Span2, ty: &str) -> Option<Result<Self, Error>> {
        let Some(("", width)) = ty.split_once('u') else {
            // This is not even an unsigned integer.
            return None;
        };
        let Ok(width) = width.parse() else {
            return Some(Err(err!(span; "failed to parse integer width suffix")));
        };
        if width == 0 {
            return Some(Err(err!(span; "'bitwise' does not support zero-sized types")));
        }

        Some(Ok(Self { width }))
    }

    /// Produces a new `UIntType` whose bit-width is 'rounded up' to the next smallest power of two
    /// that is at least 8.
    ///
    /// If the bit-width of the current type is a power of two and at least 8, then an equivalent
    /// `UIntType` is returned. Otherwise, the bit-width of the new type is guaranteed to be a power
    /// of two that is at least 8 and is strictly greater than the current width.
    ///
    /// *However*, this method does not guarantee that the new type [exists]. For example, if the
    /// current bit-width is 255, then a `UIntType` of width 256 will be returned despite the
    /// nonexistence of the `u256` primitive.
    ///
    /// [exists]: Self::exists
    pub(crate) fn round_up(self) -> Self {
        let width = if self.width <= 8 {
            8
        } else {
            // This is the integer component of `log2(width)`, which I will call the 'magnitude'.
            let mag = self.width.ilog2() as usize;
            // This is the fractional component of `log2(width)`, which I will call the 'remainder'.
            let rem = self.width & ((1 << mag) - 1);

            if rem == 0 {
                // `self.width` is already a power of two.
                self.width
            } else {
                1 << (mag + 1)
            }
        };

        Self { width }
    }

    /// Determines if this type represents an unsigned integer primitive that exists in Rust today.
    ///
    /// This returns `true` if [the width] of this type is a power of two between 8 and 128,
    /// inclusive, and `false` otherwise.
    ///
    /// [the width]: Self::width
    pub(crate) fn exists(self) -> bool {
        match self.width {
            8 | 16 | 32 | 64 | 128 => true,
            _ => false,
        }
    }

    /// Produces an identifier of the form <code>u&nbsp;<em>width</em></code> with the given span.
    pub(crate) fn make_ident(self, span: Span2) -> syn::Ident {
        syn::Ident::new(&format!("u{}", self.width), span)
    }
}

/// Returns the best representation for an item.
///
/// If `item_attrs` contains a `repr` attribute, its argument is parsed as a [`UIntType`]. If
/// successful, the attribute is first removed from `item_attrs` so it will not appear in the
/// generated item, and then the attribute argument is returned.
///
/// Otherwise, `expected_width` and `item_width` are consulted, in that order, to generate
/// `UIntType`s of those widths. This function ultimately fails if `item_width` is a compile-time
/// expression (indeterminate at macro evaluation time) and all previous strategies have been
/// exhausted, in which case an [`Error`] is returned.
fn determine_item_repr(
    expected_width: Option<usize>,
    item_span: Span2,
    item_attrs: &mut Vec<syn::Attribute>,
    item_width: &Width,
) -> Result<Repr, Error> {
    if let Some((i, attr)) =
        item_attrs.iter().enumerate().find(|(_, attr)| attr.path().is_ident("repr"))
    {
        let (ty, span) = match attr.parse_args::<syn::Ident>() {
            Ok(it) => (it.to_string(), it.span()),
            Err(e) => {
                return Err(Error::new(e));
            }
        };
        let repr = match Repr::parse(span, &ty) {
            Some(Ok(it)) => {
                if !it.exists() {
                    return Err(err!(span; "attribute argument cannot be an imaginary type"));
                }

                it
            }
            Some(Err(e)) => {
                return Err(e);
            }
            None => {
                return Err(err!(span; "attribute argument must be an unsigned integer primitive"));
            }
        };
        item_attrs.remove(i);

        Ok(repr)
    } else {
        let repr = if let Some(width) = expected_width {
            Repr { width }
        } else {
            match item_width {
                Width::Met { value, .. } => Repr { width: *value },
                Width::Ct(_) => {
                    return Err(err!(
                        item_span;
                        "not enough information to compute item width at macro evaluation time",
                    ));
                }
            }
        }
        .round_up();
        if !repr.exists() {
            return Err(err!(
                item_span;
                "item cannot be represented by any unsigned integer primitive",
            ));
        }

        Ok(repr)
    }
}
