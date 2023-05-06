// SPDX-License-Identifier: MPL-2.0

//! An inner type in a [tuple] or [array].
//!
//! [tuple]: Type::Tuple
//! [array]: Type::Array

use super::*;

/// An inner type in a [tuple] or [array].
///
/// [tuple]: Type::Tuple
/// [array]: Type::Array
#[derive(Clone)]
pub(crate) enum ElemType {
    /// A boolean: `bool`.
    Bool(Span2),
    /// A [`UIntType`].
    UInt(Span2, UIntType),
    /// A user-defined type that implements the `Bitwise` trait.
    ImplBitwise(syn::TypePath),
}

impl ElemType {
    /// The bit-width of this type.
    pub(crate) fn width(self) -> Width {
        match self {
            Self::Bool(span) => Width::Met { span, value: 1 },
            Self::UInt(span, ty) => Width::Met { span, value: ty.width() },
            Self::ImplBitwise(ty) => Width::Ct(su::expr::make_bitwise_width(ty.span(), ty.into())),
        }
    }

    pub(crate) fn parse(span: Span2, ty: syn::TypePath) -> Result<Self, TokenStream> {
        if let Some(ty) = ty.path.get_ident().map(ToString::to_string) {
            if ty == "bool" {
                return Ok(Self::Bool);
            } else if let Some(result) = UIntType::parse(span, &ty) {
                return result.map(Self::UInt);
            }
        }

        Ok(Self::Other(ty))
    }

    pub(crate) fn as_rust_primitive(self) -> Self {
        match self {
            Self::UInt(ty) => Self::UInt(ty.round_up()),
            _ => self,
        }
    }

    pub(crate) fn exists(&self) -> bool {
        match self {
            Self::UInt(ty) => ty.exists(),
            _ => true,
        }
    }
}

impl From<PrimeType> for syn::TypePath {
    fn from(ty: PrimeType) -> Self {
        match ty {
            Self::Bool => Self { qself: None, path: ["bool"].into_iter().collect() },
            Self::UInt(ty) => ty.into(),
            Self::Other(ty) => ty,
        }
    }
}
