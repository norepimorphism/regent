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
    /// Attempts to parse an `ElemType` from the given [`syn::TypePath`].
    pub(crate) fn parse(ty: syn::TypePath) -> Result<Self, Error> {
        let span = ty.span();
        if let Some(ty) = ty.path.get_ident().map(ToString::to_string) {
            if ty == "bool" {
                return Ok(Self::Bool(span));
            }
            if let Some(result) = UIntType::parse(span, &ty) {
                return result.map(|ty| Self::UInt(span, ty));
            }
        }

        // Because we can't determinate at macro evaluation time if `ty` indeed implements
        // `Bitwise`, we give the benefit of the doubt.
        Ok(Self::ImplBitwise(ty))
    }

    /// Attempts to losslessly convert this type into a valid API type.
    ///
    /// This method only has an effect if this type is [`UInt`] and has a bit-width that is less
    /// than 8 or not a power of two. In that case, the inner [`UIntType`] is rounded up according
    /// to [`round_up`]. An error is returned only if the `UIntType` does not [exist] after
    /// rounding.
    ///
    /// [`UInt`]: Self::UInt
    /// [`round_up`]: UIntType::round_up
    /// [exist]: UIntType::exists
    pub(crate) fn try_into_api_type(self) -> Result<Self, Error> {
        match self {
            Self::UInt(span, ty) => {
                let ty = ty.round_up();

                if ty.exists() {
                    Ok(Self::UInt(span, ty))
                } else {
                    // FIXME: improve error message
                    Err(err!(span; "this cannot be made into an API type"))
                }
            }
            _ => Ok(self),
        }
    }

    /// The span of this type.
    pub(crate) fn span(&self) -> Span2 {
        match self {
            Self::Bool(span) => *span,
            Self::UInt(span, _) => *span,
            Self::ImplBitwise(ty) => ty.span(),
        }
    }

    /// The bit-width of this type.
    pub(crate) fn width(self) -> Width {
        match self {
            Self::Bool(span) => Width::Met(span, 1),
            Self::UInt(span, ty) => Width::Met(span, ty.width()),
            Self::ImplBitwise(ty) => Width::Ct({
                let span = ty.span();

                syn::ExprPath {
                    attrs: vec![],
                    qself: Some(syn::QSelf {
                        lt_token: syn::Token![<](span),
                        ty: Box::new(ty),
                        position: 2,
                        as_token: Some(syn::Token![as](span)),
                        gt_token: syn::Token![>](span),
                    }),
                    path: path!(span; ::regent::Bitwise::WIDTH),
                }
                .into()
            }),
        }
    }

    /// Determines if this type exists.
    ///
    /// This method returns `false` only when this type is [`UInt`] and the inner [`UIntType`] does
    /// not [exist].
    ///
    /// [`UInt`]: Self::UInt
    /// [exist]: UIntType::exists
    pub(crate) fn exists(&self) -> bool {
        match self {
            Self::Bool(_) => true,
            Self::UInt(_, ty) => ty.exists(),
            // Because we can't determine at macro evaluation time if the type exists, we give the
            // benefit of the doubt.
            Self::ImplBitwise(_) => true,
        }
    }
}

impl From<ElemType> for syn::Type {
    fn from(ty: ElemType) -> Self {
        syn::TypePath::from(ty).into()
    }
}

impl From<ElemType> for syn::TypePath {
    fn from(ty: ElemType) -> Self {
        match ty {
            ElemType::Bool(span) => Self { qself: None, path: syn::Ident::new("bool", span).into() },
            ElemType::UInt(span, ty) => Self { qself: None, path: syn::Ident::new(&ty.to_string(), span).into() },
            ElemType::ImplBitwise(ty) => ty,
        }
    }
}
