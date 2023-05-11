// SPDX-License-Identifier: MPL-2.0

use super::*;

#[derive(Default)]
pub(super) struct Args {
    pub(super) constant: Option<syn::Expr>,
}

impl Args {
    pub(super) fn parse(attrs: &mut Vec<syn::Attribute>) -> Result<Self, Error> {
        let mut result = Self::default();

        let mut i = 0;
        while i < attrs.len() {
            match unsafe { attrs.get_unchecked(i) }.meta {
                syn::Meta::Path(path) if path.is_ident("constant") => {
                    let span = path.span();
                    let value = || {
                        let func_qself = syn::QSelf {
                            lt_token: syn::Token![<](span),
                            ty: Box::new(syn::TypeInfer { underscore_token: syn::Token![_](span) }.into()),
                            position: 3,
                            as_token: Some(syn::Token![as](span)),
                            gt_token: syn::Token![>](span),
                        };
                        let func = syn::ExprPath {
                            attrs: vec![],
                            qself: Some(func_qself),
                            path: path!(span; ::core::default::Default::default),
                        }
                        .into();
                        let value = syn::ExprCall {
                            attrs: vec![],
                            func: Box::new(func),
                            paren_token: syn::token::Paren(span),
                            args: Punctuated::new(),
                        }
                        .into();

                        Ok(value)
                    };
                    Self::set_field(span, &mut result.constant, value)?;
                }
                syn::Meta::NameValue(pair) if pair.path.is_ident("constant") => {
                    Self::set_field(pair.span(), &mut result.constant, || Ok(pair.value))?;
                }
                _ => {
                    i += 1;
                    continue;
                }
            }

            attrs.remove(i);
        }

        Ok(result)
    }

    fn set_field<T>(
        span: Span2,
        field: &mut Option<T>,
        value: impl FnOnce() -> Result<T, Error>,
    ) -> Result<(), Error> {
        if field.is_some() {
            return Err(err!(span; "attribute is a duplicate"));
        }
        *field = Some(value()?);

        Ok(())
    }
}

/// The type of a struct field.
#[derive(Clone)]
pub(super) enum Type {
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
    pub(super) fn parse(ty: syn::Type) -> Result<Self, Error> {
        match ty {
            syn::Type::Path(elem) => ElemType::parse(elem).map(Self::Elem),
            syn::Type::Tuple(tuple) => Self::parse_tuple(tuple.span(), tuple.elems),
            syn::Type::Array(array) => Self::parse_array(array.span(), *array.elem, array.len),
            _ => Err(err!(ty.span(); "field type is not supported")),
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
        if elems.is_empty() {
            return Err(err!(span; "tuple cannot have zero elements"));
        }

        Ok(Self::Tuple(span, elems))
    }

    fn parse_array(span: Span2, elem: syn::Type, len: syn::Expr) -> Result<Self, Error> {
        let syn::Type::Path(elem) = elem else {
            return Err(err!(elem.span(); "array element must be a path"));
        };
        let elem = ElemType::parse(elem)?;

        let len_span = len.span();
        let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(len), .. }) = len else {
            return Err(err!(len_span; "array length must be an integer literal"));
        };
        let len = len.base10_parse().map_err(Error)?;
        if len == 0 {
            return Err(err!(len_span; "array length cannot be zero"));
        }

        Ok(Self::Array { span, elem, len })
    }

    /// Attempts to convert this type into an API type.
    pub(super) fn try_into_api_type(self) -> Result<Self, Error> {
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
    pub(super) fn span(&self) -> Span2 {
        match self {
            Self::Elem(elem) => elem.span(),
            Self::Tuple(span, _) => *span,
            Self::Array { span, .. } => *span,
        }
    }

    /// The bit-width of this type.
    pub(super) fn width(self) -> Width {
        match self {
            Self::Elem(elem) => elem.width(),
            Self::Tuple(span, elems) => elems.into_iter().fold(
                Width::zero(span),
                |acc, elem| Width::add(acc, elem.width()),
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
    pub(super) fn exists(&self) -> bool {
        match self {
            Self::Elem(elem) => elem.exists(),
            Self::Tuple(_, elems) => elems.iter().all(ElemType::exists),
            Self::Array { elem, .. } => elem.exists(),
        }
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

/// An inner type in a [tuple] or [array].
///
/// [tuple]: Type::Tuple
/// [array]: Type::Array
#[derive(Clone)]
pub(super) enum ElemType {
    /// A boolean: `bool`.
    Bool(Span2),
    /// A [`uint::PseudoType`].
    UInt(Span2, uint::PseudoType),
    /// A user-defined type that implements the `Bitwise` trait.
    ImplBitwise(syn::TypePath),
}

impl ElemType {
    /// Attempts to parse an `ElemType` from the given [`syn::TypePath`].
    pub(super) fn parse(ty: syn::TypePath) -> Result<Self, Error> {
        let span = ty.span();
        if let Some(ident) = ty.path.get_ident() {
            if ident == "bool" {
                return Ok(Self::Bool(span));
            }
            if let Some(result) = uint::PseudoType::parse(ident) {
                return result.map(|ty| Self::UInt(span, ty));
            }
        }

        // We can't determinate at macro evaluation time if `ty` implements `Bitwise`, so we give
        // the benefit of the doubt.
        Ok(Self::ImplBitwise(ty))
    }

    /// Attempts to convert this type into an API type.
    pub(super) fn try_into_api_type(self) -> Result<Self, Error> {
        match self {
            Self::UInt(span, mut ty) => {
                ty.round_up();

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
    pub(super) fn span(&self) -> Span2 {
        match self {
            Self::Bool(span) => *span,
            Self::UInt(span, _) => *span,
            Self::ImplBitwise(ty) => ty.span(),
        }
    }

    /// The bit-width of this type.
    pub(super) fn width(self) -> Width {
        match self {
            Self::Bool(span) => Width::Met(span, 1),
            Self::UInt(span, ty) => Width::Met(span, ty.width()),
            Self::ImplBitwise(ty) => Width::Ct({
                let span = ty.span();

                syn::ExprPath {
                    attrs: vec![],
                    qself: Some(syn::QSelf {
                        lt_token: syn::Token![<](span),
                        ty: Box::new(ty.into()),
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
    pub(super) fn exists(&self) -> bool {
        match self {
            Self::Bool(_) => true,
            Self::UInt(_, ty) => ty.exists(),
            // We can't determine at macro evaluation time if the type exists, so we give the
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
            ElemType::Bool(span) => Self { qself: None, path: path!(span; bool) },
            ElemType::UInt(span, ty) => Self { qself: None, path: syn::Ident::new(&ty.to_string(), span).into() },
            ElemType::ImplBitwise(ty) => ty,
        }
    }
}
