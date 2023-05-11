// SPDX-License-Identifier: MPL-2.0

//! Types accepted in struct field position.

mod elem;
mod uint;

pub(crate) use elem::*;
pub(crate) use uint::*;

use super::*;

/// The type of a struct field.
#[derive(Clone)]
pub(crate) enum Type {
    /// An [element type](ElemType).
    Elem(ElemType),
    /// A tuple of [element types](ElemType).
    Tuple(Span2, Vec<ElemType>),
    /// An array of [element types](ElemType).
    Array {
        /// The span.
        span: Span2,
        /// The element type.
        elem: ElemType,
        /// The number of elements.
        len: usize,
    },
}

impl Type {
    /// Attempts to parse a `Type` from the given [`syn::Type`].
    pub(crate) fn parse(ty: syn::Type) -> Result<Self, Error> {
        match ty {
            syn::Type::Path(elem) => ElemType::parse(elem).map(Self::Elem),
            syn::Type::Tuple(tuple) => Self::parse_tuple(tuple.span(), tuple.elems),
            syn::Type::Array(array) => Self::parse_array(array.span(), *array.elem, array.len),
            _ => Err(err!(ty.span(); "type is not supported")),
        }
    }

    fn parse_tuple(span: Span2, elems: impl IntoIterator<Item = syn::Type>) -> Result<Self, Error> {
        let elems = elems
            .into_iter()
            .map(|elem| {
                if let syn::Type::Path(elem) = elem {
                    ElemType::parse(elem)
                } else {
                    Err(err!(elem.span(); "tuple element must be a path"))
                }
            })
            .collect::<Result<Vec<ElemType>, _>>()?;

        Ok(Self::Tuple(span, elems))
    }

    fn parse_array(span: Span2, elem: syn::Type, len: syn::Expr) -> Result<Self, Error> {
        let syn::Type::Path(elem) = elem else {
            return Err(err!(elem.span(); "array element must be a path"));
        };
        let elem = ElemType::parse(elem)?;
        let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(len), .. }) = len else {
            return Err(err!(len.span(); "array length must be an integer literal"));
        };
        let len = len.base10_parse().map_err(Error)?;

        Ok(Self::Array { span, elem, len })
    }

    /// Attempts to losslessly convert this type into a valid API type.
    pub(crate) fn try_into_api_type(self) -> Result<Self, Error> {
        match self {
            Self::Elem(elem) => elem.try_into_api_type().map(Self::Elem),
            Self::Tuple(span, elems) => elems.into_iter()
                .map(|elem| elem.try_into_api_type())
                .collect::<Result<_, _>>()
                .map(|elems| Self::Tuple(span, elems)),
            Self::Array { span, elem, len } => elem.try_into_api_type()
                .map(|elem| Self::Array { span, elem, len }),
        }
    }

    /// The span of this type.
    pub(crate) fn span(&self) -> Span2 {
        match self {
            Self::Elem(elem) => elem.span(),
            Self::Tuple(span, _) => *span,
            Self::Array { span, .. } => *span,
        }
    }

    /// The bit-width of this type.
    pub(crate) fn width(self) -> Width {
        match self {
            Self::Elem(elem) => elem.width(),
            Self::Tuple(span, elems) => elems.into_iter().fold(
                Width::zero(span),
                |acc, elem| match (acc, elem.width()) {
                    (Width::Met(_, lhs), Width::Met(_, rhs)) => {
                        Width::Met(span, lhs + rhs)
                    }
                    (lhs, rhs) => Width::Ct(syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(lhs.into_expr()),
                        op: syn::BinOp::Add(syn::Token![+](span)),
                        right: Box::new(rhs.into_expr()),
                    }.into()),
                },
            ),
            Self::Array { span, elem, len } => match elem.width() {
                Width::Met(_, elem_width) => Width::Met(span, elem_width * len),
                Width::Ct(elem_width) => Width::Ct(syn::ExprBinary {
                    attrs: vec![],
                    left: Box::new(elem_width),
                    op: syn::BinOp::Mul(syn::Token![*](span)),
                    right: Box::new(syn::ExprLit {
                        attrs: vec![],
                        lit: syn::LitInt::new(&len.to_string(), span).into(),
                    }.into()),
                }.into()),
            },
        }
    }

    /// Determines if this type exists.
    pub(crate) fn exists(&self) -> bool {
        match self {
            Self::Elem(elem) => elem.exists(),
            Self::Tuple(_, elems) => elems.iter().all(ElemType::exists),
            Self::Array { elem, .. } => elem.exists(),
        }
    }

    pub(crate) fn validate(&self) -> Result<(), Error> {
        match self {
            Type::Tuple(span, elems) => {
                if elems.is_empty() {
                    return Err(err!(*span; "struct field cannot be the unit type"));
                }
            }
            Type::Array { span, len, .. } => {
                if *len == 0 {
                    return Err(err!(*span; "struct field cannot be zero-sized"));
                }
            }
            _ => {}
        }

        Ok(())
    }
}

impl From<Type> for syn::Type {
    fn from(ty: Type) -> Self {
        match ty {
            Type::Elem(elem) => elem.into(),
            Type::Tuple(span, elems) => syn::TypeTuple {
                paren_token: syn::token::Paren(span),
                elems: elems.into_iter().map(syn::Type::from).collect(),
            }
            .into(),
            Type::Array { span, elem, len } => syn::TypeArray {
                bracket_token: syn::token::Bracket(span),
                elem: Box::new(elem.into()),
                semi_token: syn::Token![;](span),
                len: syn::ExprLit {
                    attrs: vec![],
                    lit: syn::LitInt::new(&len.to_string(), span).into(),
                }.into(),
            }
            .into(),
        }
    }
}
