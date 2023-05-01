// SPDX-License-Identifier: MPL-2.0

use super::*;

#[derive(Clone)]
pub(crate) enum PrimeType {
    Bool,
    UInt(UIntType),
    Other(syn::TypePath),
}

impl PrimeType {
    pub(crate) fn width(&self) -> Width {
        match self {
            Self::Bool => Width::Lit(1),
            Self::UInt(ty) => Width::Lit(ty.width),
            Self::Other(ty) => Width::Expr(quote!(<#ty as ::regent::Bitwise>::WIDTH)),
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
