// SPDX-License-Identifier: MPL-2.0

//! Types recognized by the *bitwise* macro.

mod prime;
mod uint;

pub(crate) use prime::*;
pub(crate) use uint::*;

use super::*;

/// The type of a struct field.
#[derive(Clone)]
enum Type {
    /// A [prime type](PrimeType).
    Prime(PrimeType),
    /// A tuple of [prime types](PrimeType).
    Tuple(Vec<PrimeType>),
    /// An array of [prime types](PrimeType).
    Array {
        /// The element type.
        ty: PrimeType,
        /// The number of elements.
        len: usize,
    },
}

impl Type {
    fn parse(span: Span2, ty: syn::Type) -> Result<Self, Error> {
        match ty {
            syn::Type::Path(ty) => PrimeType::parse(span, ty).map(Self::Prime),
            syn::Type::Tuple(syn::TypeTuple { elems: tys, .. }) => {
                let tys = tys
                    .into_iter()
                    .map(|ty| {
                        if let syn::Type::Path(ty) = ty {
                            PrimeType::parse(span, ty)
                        } else {
                            Err(err!(span; "tuple element type must be a path"))
                        }
                    })
                    .collect::<Result<Vec<PrimeType>, _>>()?;

                Ok(Self::Tuple(tys))
            }
            syn::Type::Array(syn::TypeArray { elem: ty, len, .. }) => {
                let syn::Type::Path(ty) = *ty else {
                    return Err(err!(span; "array element type must be a path"));
                };
                let ty = PrimeType::parse(span, ty)?;
                let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(len), .. }) = len else {
                    return Err(err!(span; "array length must be an integer literal"));
                };
                let len =
                    len.base10_parse().map_err(|e| TokenStream::from(e.into_compile_error()))?;

                Ok(Self::Array { ty, len })
            }
            _ => Err(err!(span; "unsupported type")),
        }
    }

    fn as_rust_primitives(self) -> Self {
        match self {
            Self::Prime(ty) => Self::Prime(ty.as_rust_primitive()),
            Self::Tuple(tys) => {
                Self::Tuple(tys.into_iter().map(|it| it.as_rust_primitive()).collect())
            }
            Self::Array { ty, len } => Self::Array { ty: ty.as_rust_primitive(), len },
        }
    }

    fn exists(&self) -> bool {
        match self {
            Self::Prime(ty) => ty.exists(),
            Self::Tuple(tys) => tys.iter().all(PrimeType::exists),
            Self::Array { ty, .. } => ty.exists(),
        }
    }

    fn width(&self) -> Width {
        match self {
            Self::Prime(ty) => ty.width(),
            Self::Tuple(tys) => tys.iter().map(PrimeType::width).sum(),
            Self::Array { ty, len } => ty.width() * Width::Lit(*len),
        }
    }

    fn validate(&self, span: Span2) -> Result<(), Error> {
        match self {
            Type::Tuple(tys) => {
                if tys.is_empty() {
                    return Err(err!(span; "'bitwise' fields cannot be the unit type"));
                }
            }
            Type::Array { len, .. } => {
                if *len == 0 {
                    return Err(err!(span; "'bitwise' fields cannot be zero-sized arrays"));
                }
            }
            _ => {}
        }

        Ok(())
    }
}

impl ToTokens for Type {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            Self::Prime(ty) => {
                ty.to_tokens(tokens);
            }
            Self::Tuple(tys) => {
                tokens.extend(quote! { ( #(#tys),* ) });
            }
            Self::Array { ty, len } => {
                tokens.extend(quote! { [#ty; #len] });
            }
        }
    }
}
