// SPDX-License-Identifier: MPL-2.0

//! Struct fields.
//!
//! # Pseudo-types
//!
//! This module uses the term 'pseudo-type', or type 'as written', to mean a type permissible in
//! [`bitwise!`] struct field syntax that may or may not actually exist in Rust. The imaginary `u7`,
//! `(bool, u2)`, and `[u3; 5]` are all pseudo-types, as are the Rust types `u8`, `(bool, u8)`, and
//! `[u8; 5]`.
//!
//! Pseudo-types are modeled by [`PseudoType`].
//!
//! # API Types
//!
//! This module uses the term 'API type' to mean an existing Rust type (i.e., expressible as
//! [`syn::Type`]) that corresponds to a pseudo-type and which can constitute any valid bit pattern
//! of the pseudo-type. Analogy: if a [`uint::RustType`] is the representation for an emitted item,
//! then an API type is the representation for a struct field.
//!
//! API types are modeled by [`syn::Type`].

use super::*;

/// Models a struct field.
pub(super) struct Field {
    /// The value associated with the `#[constant]` attribute, if present.
    pub(super) constant: Option<syn::Expr>,
    /// The span covering the entire field, excluding any trailing comma.
    pub(super) span: Span2,
    /// The outer attributes, excluding those parsed by [`Attrs::parse`].
    pub(super) attrs: Vec<syn::Attribute>,
    /// The visibility.
    pub(super) vis: syn::Visibility,
    /// The name of the field, or `f{index}` if unnamed.
    pub(super) ident: syn::Ident,
    /// The [pseudo-type], or type 'as written'.
    ///
    /// [pseudo-type]: index.html#pseudo-types
    pub(super) pseudo_ty: PseudoType,
}

impl Field {
    /// Attempts to parse a `Field` from a [`syn::Field`].
    ///
    /// # Arguments
    ///
    /// `i` is the index of this field. An index of 0 corresponds to the most-significant field, and
    /// each subsequent next most-significant field increments the index by one.
    ///
    /// `field` is the [`syn::Field`]. This function consumes it by-move.
    ///
    /// # Errors
    ///
    /// An error is returned if [`field.ty`] fails [`PseudoType::parse`] or [`field.attrs`] fails
    /// [`Attrs::parse`].
    ///
    /// [`field.ty`]: syn::Field::ty
    /// [`field.attrs`]: syn::Field::attrs
    pub(super) fn parse(i: usize, mut field: syn::Field) -> Result<Self> {
        let span = field.span();
        let attrs = Attrs::parse(&mut field.attrs)?;

        Ok(Self {
            constant: attrs.constant,
            span,
            attrs: field.attrs,
            vis: field.vis,
            ident: field.ident.unwrap_or_else(|| syn::Ident::new(&format!("f{i}"), span)),
            pseudo_ty: PseudoType::parse(field.ty)?,
        })
    }
}

/// Models outer attributes on a struct field that are recognized specially by [`bitwise!`].
#[derive(Default)]
pub(super) struct Attrs {
    /// The value associated with the `#[constant]` attribute, if present.
    constant: Option<syn::Expr>,
}

impl Attrs {
    /// Attempts to parse outer attributes on a struct field.
    ///
    /// # Arguments
    ///
    /// `attrs` is a mutably borrowed vector of [`syn::Attribute`]s. Attributes specific to
    /// [`bitwise!`] are parsed and then removed from the vector, and all other attributes are
    /// ignored and left as-is.
    ///
    /// # Errors
    ///
    /// TODO
    pub(super) fn parse(attrs: &mut Vec<syn::Attribute>) -> Result<Self> {
        let mut result = Self::default();

        let mut i = 0;
        while i < attrs.len() {
            // FIXME: we can use `Option::get_unchecked`, but we have to be very careful
            let attr = attrs.get(i).unwrap();
            if !attr.path().is_ident("constant") {
                i += 1;
                continue;
            }
            if result.constant.is_some() {
                return Err(err!(attr.span(); "attribute is a duplicate"));
            }

            let attr = attrs.remove(i);
            result.constant = Some(match attr.meta {
                syn::Meta::List(list) => {
                    return Err(err!(list.span(); "attribute does not support list syntax"));
                }
                syn::Meta::NameValue(pair) => pair.value,
                syn::Meta::Path(path) => {
                    let span = path.span();

                    let func_qself = syn::QSelf {
                        lt_token: syn::Token![<](span),
                        ty: Box::new(
                            syn::TypeInfer { underscore_token: syn::Token![_](span) }.into(),
                        ),
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

                    // Rendered:
                    //   <_ as ::core::default::Default>::default()
                    syn::ExprCall {
                        attrs: vec![],
                        func: Box::new(func),
                        paren_token: syn::token::Paren(span),
                        args: Punctuated::new(),
                    }
                    .into()
                }
            });
        }

        Ok(result)
    }
}

/// Models the type of [a struct field] 'as written'.
///
/// This type corresponds to the *&lt;type&gt;* syntactical rule from the struct specification.
///
/// This type is [spanned]. The associated span can be obtained from the [`span`] method.
///
/// [a struct field]: Field
/// [spanned]: Span2
/// [`span`]: Self::Span
#[derive(Clone)]
pub(super) enum PseudoType {
    /// An [element type].
    ///
    /// [element type]: PseudoElemType
    Elem(PseudoElemType),
    /// A [tuple type].
    ///
    /// [tuple type]: PseudoTupleType
    Tuple(PseudoTupleType),
    /// An [array type].
    ///
    /// [array type]: PseudoArrayType
    Array(PseudoArrayType),
}

impl PseudoType {
    /// Attempts to parse a `Type` from a [`syn::Type`].
    ///
    /// # Errors
    ///
    /// An error is returned if `ty` is not [a path], [tuple], or [array], or if one of
    /// [`PseudoElemType::parse], [`PseudoTupleType::parse`], or [`PseudoArrayType::parse`] fail.
    ///
    /// [a path]: syn::TypePath
    /// [tuple]: syn::TypeTuple
    /// [array]: syn::TypeArray
    pub(super) fn parse(ty: syn::Type) -> Result<Self> {
        match ty {
            syn::Type::Path(elem) => PseudoElemType::parse(elem).map(Self::Elem),
            syn::Type::Tuple(tuple) => PseudoTupleType::parse(tuple.span(), tuple.elems).map(Self::Tuple),
            syn::Type::Array(array) => PseudoArrayType::parse(array.span(), *array.elem, array.len).map(Self::Array),
            _ => Err(err!(ty.span(); "field type is not supported")),
        }
    }

    /// The span of this type.
    pub(super) fn span(&self) -> Span2 {
        match self {
            Self::Elem(ty) => ty.span(),
            Self::Tuple(ty) => ty.span(),
            Self::Array(ty) => ty.span(),
        }
    }

    /// The bit-width of this type.
    pub(super) fn width(&self) -> Width {
        match self {
            Self::Elem(ty) => ty.width(),
            Self::Tuple(ty) => ty.width(),
            Self::Array(ty) => ty.width(),
        }
    }

    /// Attempts to convert this into an [API type].
    ///
    /// [API Type]: index.html#api-types
    pub(super) fn try_into_api_type(self) -> Option<syn::Type> {
        match self {
            Self::Elem(ty) => ty.try_into_api_type(),
            Self::Tuple(ty) => ty.try_into_api_type(),
            Self::Array(ty) => ty.try_into_api_type(),
        }
    }
}

/// A tuple of [element types].
///
/// [element types]: PseudoElemType
#[derive(Clone)]
pub(super) struct PseudoTupleType {
    span: Span2,
    elems: Vec<PseudoElemType>,
}

impl PseudoTupleType {
    /// Attempts to parse a `PseudoTupleType` from a sequence of [`syn::Type`]s.
    ///
    /// # Arguments
    ///
    /// `span` is the span covering the entire tuple (the parentheses and everything between them).
    /// `elems` is an iterator over the tuple elements in left-to-right order.
    ///
    /// # Errors
    ///
    /// An error is returned if the `elems` iterator is empty or any element fails [to parse].
    ///
    /// [to parse]: PseudoElemType::parse
    pub(super) fn parse(span: Span2, elems: impl IntoIterator<Item = syn::Type>) -> Result<Self> {
        let elems: Vec<PseudoElemType> = elems
            .into_iter()
            .map(|elem| {
                if let syn::Type::Path(elem) = elem {
                    PseudoElemType::parse(elem)
                } else {
                    Err(err!(elem.span(); "tuple element must be a path"))
                }
            })
            .collect::<Result<_>>()?;
        if elems.is_empty() {
            return Err(err!(span; "tuple cannot have zero elements"));
        }

        Ok(Self { span, elems })
    }

    /// The span of this type.
    pub(super) fn span(&self) -> Span2 {
        self.span
    }

    /// The bit-width of this type.
    pub(super) fn width(&self) -> Width {
        self.elems.iter().fold(Width::Met(self.span, 0), |acc, elem| Width::add(acc, elem.width()))
    }

    /// Attempts to convert this into an [API type].
    ///
    /// [API Type]: index.html#api-types
    pub(super) fn try_into_api_type(self) -> Option<syn::Type> {
        self.elems
            .into_iter()
            .map(PseudoElemType::try_into_api_type)
            .collect::<Option<Punctuated<_, _>>>()
            .map(|elems| syn::TypeTuple { paren_token: syn::token::Paren(self.span), elems }.into())
    }
}

/// An array of [element types].
///
/// [element types]: PseudoElemType
#[derive(Clone)]
pub(super) struct PseudoArrayType {
    /// The span.
    span: Span2,
    /// The element type.
    elem: PseudoElemType,
    /// The number of elements.
    len: usize,
}

impl PseudoArrayType {
    /// Attempts to parse a `PseudoArrayType`.
    pub(super) fn parse(span: Span2, elem: syn::Type, len: syn::Expr) -> Result<Self> {
        let syn::Type::Path(elem) = elem else {
            return Err(err!(elem.span(); "array element must be a path"));
        };
        let elem = PseudoElemType::parse(elem)?;
        let len = {
            let span = len.span();
            let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(len), .. }) = len else {
                return Err(err!(span; "array length must be an integer literal"));
            };
            let len = len.base10_parse().map_err(Error)?;
            if len == 0 {
                return Err(err!(span; "array length cannot be zero"));
            }

            len
        };

        Ok(Self { span, elem, len })
    }

    /// The span of this type.
    pub(super) fn span(&self) -> Span2 {
        self.span
    }

    /// The bit-width of this type.
    pub(super) fn width(&self) -> Width {
        Width::mul(self.elem.width(), Width::Met(self.span, self.len))
    }

    /// Attempts to convert this into an [API type].
    ///
    /// [API Type]: index.html#api-types
    pub(super) fn try_into_api_type(self) -> Option<syn::Type> {
        self.elem.try_into_api_type().map(|elem| {
            let span = self.span;

            syn::TypeArray {
                bracket_token: syn::token::Bracket(span),
                elem: Box::new(elem.into()),
                semi_token: syn::Token![;](span),
                len: syn::ExprLit {
                    attrs: vec![],
                    lit: syn::LitInt::new(&self.len.to_string(), span).into(),
                }
                .into(),
            }
            .into()
        })
    }
}

/// An inner type in a [tuple] or [array].
///
/// This is a [pseudo-type].
///
/// This type is [spanned]. The associated span can be obtained from the [`span`] method.
///
/// [tuple]: PseudoTupleType
/// [array]: PseudoArrayType
/// [pseudo-type]: index.html#pseudo-types
/// [spanned]: Span2
/// [`span`]: Self::span
#[derive(Clone)]
pub(super) enum PseudoElemType {
    /// A boolean: `bool`.
    Bool(Span2),
    /// A [`uint::PseudoType`].
    UInt(Span2, uint::PseudoType),
    /// A user-defined type that implements the `Bitwise` trait.
    ImplBitwise(syn::TypePath),
}

impl PseudoElemType {
    /// Attempts to parse a `PseudoElemType` from a [`syn::TypePath`].
    pub(super) fn parse(ty: syn::TypePath) -> Result<Self> {
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

    /// The span of this type.
    pub(super) fn span(&self) -> Span2 {
        match self {
            Self::Bool(span) => *span,
            Self::UInt(span, _) => *span,
            Self::ImplBitwise(ty) => ty.span(),
        }
    }

    /// The bit-width of this type.
    pub(super) fn width(&self) -> Width {
        match self {
            Self::Bool(span) => Width::Met(*span, 1),
            Self::UInt(span, ty) => Width::Met(*span, ty.width()),
            Self::ImplBitwise(ty) => Width::Ct({
                let span = ty.span();

                // Rendered:
                //   <#ty as :regent::Bitwise>::WIDTH
                syn::ExprPath {
                    attrs: vec![],
                    qself: Some(syn::QSelf {
                        lt_token: syn::Token![<](span),
                        // It seems bad that we clone here, but the clone implementation used should
                        // actually be equivalent to a copy. This is because the only type contained
                        // in `syn::TypePath` with a non-trivial clone implementation seems to be
                        // the `syn::Ident` enum, and because we configured `proc-macro2` to wrap
                        // the compiler-provided `proc-macro` crate, all `syn::Ident`s should be
                        // wrapping `proc_macro::Ident`, which implements `Copy`.
                        ty: Box::new(ty.clone().into()),
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

    /// Attempts to convert this into an [API type].
    ///
    /// [API Type]: index.html#api-types
    pub(super) fn try_into_api_type(self) -> Option<syn::Type> {
        match self {
            Self::Bool(span) => Some(ty_path!(span; bool)),
            Self::UInt(span, mut ty) => {
                ty.round_up();
                let ty = ty.try_into_rust_type()?;

                Some(ty.into_syn_type(span))
            }
            Self::ImplBitwise(ty) => Some(ty.into()),
        }
    }
}

/// A field type that is convertible to-and-from the representation type of its owning struct.
pub(super) trait Represented {
    /// Produces a [`syn::Expr`] that extracts this field from a representation of its owning
    /// struct.
    ///
    /// # Arguments
    ///
    /// `repr_width` specifies the bit-width of the struct representation, and `repr_expr` is the
    /// expression for the representation itself.
    ///
    /// This function expects this field to already occupy the least-significant bits of the
    /// representation (i.e., the representation has been right-shifted to the position of the
    /// field).
    fn extract(&self, repr_width: usize, repr_expr: syn::Expr) -> syn::Expr;

    /// Produces a [`syn::Expr`] that zero-extends this field into a representation of its owning
    /// struct.
    ///
    /// # Arguments
    ///
    /// `repr_width` specifies the bit-width of the struct representation, and `field_expr` is the
    /// expression for the field (that is to be zero-extended).
    fn extend(&self, repr_width: usize, field_expr: syn::Expr) -> syn::Expr;
}

impl Represented for PseudoType {
    fn extract(&self, repr_width: usize, repr_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Elem(ty) => ty.extract(repr_width, repr_expr),
            Self::Tuple(ty) => ty.extract(repr_width, repr_expr),
            Self::Array(ty) => ty.extract(repr_width, repr_expr),
        }
    }

    fn extend(&self, repr_width: usize, field_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Elem(ty) => ty.extend(repr_width, field_expr),
            Self::Tuple(ty) => ty.extend(repr_width, field_expr),
            Self::Array(ty) => ty.extend(repr_width, field_expr),
        }
    }
}

impl<T: ContainerType> Represented for T {
    fn extract(&self, repr_width: usize, repr_expr: syn::Expr) -> syn::Expr {
        let span = repr_expr.span();

        // Rendered:
        //   let mut repr = #repr_expr;
        let repr_local = syn::Stmt::Local(syn::Local {
            attrs: vec![],
            let_token: syn::Token![let](span),
            pat: syn::PatIdent {
                attrs: vec![],
                by_ref: None,
                mutability: Some(syn::Token![mut](span)),
                ident: syn::Ident::new("repr", span),
                subpat: None,
            }
            .into(),
            init: Some(syn::LocalInit {
                eq_token: syn::Token![=](span),
                expr: Box::new(repr_expr),
                diverge: None,
            }),
            semi_token: syn::Token![;](span),
        });

        let tmp_elems: Punctuated<_, _> = self.iter()
            .rev()
            .map(|elem| syn::ExprBlock {
                attrs: vec![],
                label: None,
                block: syn::Block {
                    brace_token: syn::token::Brace(span),
                    stmts: vec![
                        syn::Stmt::Local(syn::Local {
                            attrs: vec![],
                            let_token: syn::Token![let](span),
                            pat: syn::PatIdent {
                                attrs: vec![],
                                by_ref: None,
                                mutability: None,
                                ident: syn::Ident::new("it", span),
                                subpat: None,
                            }
                            .into(),
                            init: Some(syn::LocalInit {
                                eq_token: syn::Token![=](span),
                                expr: Box::new(elem.extract(repr_width, expr_path!(span; repr))),
                                diverge: None,
                            }),
                            semi_token: syn::Token![;](span),
                        }),
                        syn::Stmt::Expr(
                            syn::ExprBinary {
                                attrs: vec![],
                                left: Box::new(expr_path!(span; repr)),
                                op: syn::BinOp::ShrAssign(syn::Token![>>=](span)),
                                right: Box::new(elem.width().into()),
                            }
                            .into(),
                            Some(syn::Token![;](span)),
                        ),
                        syn::Stmt::Expr(expr_path!(span; it), None),
                    ],
                },
            })
            .map(syn::Expr::from)
            .collect();
        let elems =
            (0..tmp_elems.len()).rev().map(|i| self.make_accessor(i, expr_path!(span; tmp))).collect();

        // let tmp = #tmp_elems;
        let tmp_local = syn::Stmt::Local(syn::Local {
            attrs: vec![],
            let_token: syn::Token![let](span),
            pat: syn::PatIdent {
                attrs: vec![],
                by_ref: None,
                mutability: None,
                ident: syn::Ident::new("tmp", span),
                subpat: None,
            }
            .into(),
            init: Some(syn::LocalInit {
                eq_token: syn::Token![=](span),
                expr: Box::new(self.make_container(tmp_elems)),
                diverge: None,
            }),
            semi_token: syn::Token![;](span),
        });
        let elems = syn::Stmt::Expr(self.make_container(elems), None);

        syn::ExprBlock {
            attrs: vec![],
            label: None,
            block: syn::Block {
                brace_token: syn::token::Brace(span),
                stmts: vec![repr_local, tmp_local, elems],
            },
        }
        .into()
    }

    fn extend(&self, repr_width: usize, field_expr: syn::Expr) -> syn::Expr {
        let span = field_expr.span();

        let brace_token = syn::token::Brace(span);
        let let_token = syn::Token![let](span);
        let mut_token = syn::Token![mut](span);
        let eq_token = syn::Token![=](span);
        let or_eq_token = syn::Token![|=](span);
        let semi_token = syn::Token![;](span);
        let shl_eq_token = syn::Token![<<=](span);

        // Rendered:
        //   let mut repr = 0;
        let repr_local = syn::Stmt::Local(syn::Local {
            attrs: vec![],
            let_token,
            pat: syn::PatIdent {
                attrs: vec![],
                by_ref: None,
                mutability: Some(mut_token),
                ident: syn::Ident::new("repr", span),
                subpat: None,
            }
            .into(),
            init: Some(syn::LocalInit {
                eq_token,
                expr: Box::new(
                    syn::ExprLit {
                        attrs: vec![],
                        lit: syn::LitInt::new("0", span).into(),
                    }
                    .into(),
                ),
                diverge: None,
            }),
            semi_token,
        });
        // Rendered:
        //   repr
        let repr_expr = syn::Stmt::Expr(expr_path!(span; repr), None);

        let stmts = once(repr_local).chain(self.iter().enumerate().rev().flat_map(|(i, elem)| [
            // Rendered:
            //   repr <<= /* elem.width() */;
            syn::Stmt::Expr(
                syn::ExprBinary {
                    attrs: vec![],
                    left: Box::new(expr_path!(span; repr)),
                    op: syn::BinOp::ShlAssign(shl_eq_token),
                    right: Box::new(elem.width().into()),
                }
                .into(),
                Some(semi_token),
            ),
            // Rendered:
            //   repr |= /* elem.extend() */;
            syn::Stmt::Expr(
                syn::ExprBinary {
                    attrs: vec![],
                    left: Box::new(expr_path!(span; repr)),
                    op: syn::BinOp::BitOrAssign(or_eq_token),
                    right: Box::new(elem.extend(repr_width, self.make_accessor(i, field_expr.clone()))),
                }
                .into(),
                Some(semi_token),
            ),
        ]))
        .chain(once(repr_expr))
        .collect();

        syn::ExprBlock {
            attrs: vec![],
            label: None,
            block: syn::Block { brace_token, stmts }
        }
        .into()
    }
}

trait ContainerType {
    type Elements<'a>: Iterator<Item = &'a PseudoElemType> + DoubleEndedIterator + ExactSizeIterator
    where
        Self: 'a;

    fn iter<'a>(&'a self) -> Self::Elements<'a>;

    fn make_container(&self, elems: Punctuated<syn::Expr, syn::Token![,]>) -> syn::Expr;

    fn make_accessor(&self, i: usize, base: syn::Expr) -> syn::Expr;
}

impl ContainerType for PseudoTupleType {
    type Elements<'a> = std::slice::Iter<'a, PseudoElemType>;

    fn iter<'a>(&'a self) -> Self::Elements<'a> {
        self.elems.iter()
    }

    fn make_container(&self, elems: Punctuated<syn::Expr, syn::Token![,]>) -> syn::Expr {
        syn::ExprTuple { attrs: vec![], paren_token: syn::token::Paren(self.span), elems }.into()
    }

    fn make_accessor(&self, i: usize, base: syn::Expr) -> syn::Expr {
        syn::ExprField {
            attrs: vec![],
            base: Box::new(base),
            dot_token: syn::Token![.](self.span),
            member: syn::Member::Unnamed(syn::Index {
                index: u32::try_from(i).unwrap(),
                span: self.span,
            }),
        }
        .into()
    }
}

impl ContainerType for PseudoArrayType {
    type Elements<'a> = PseudoArrayIter<'a>;

    fn iter<'a>(&'a self) -> Self::Elements<'a> {
        PseudoArrayIter { elem: &self.elem, rem: self.len }
    }

    fn make_container(&self, elems: Punctuated<syn::Expr, syn::Token![,]>) -> syn::Expr {
        syn::ExprArray {
            attrs: vec![],
            bracket_token: syn::token::Bracket(self.span),
            elems,
        }
        .into()
    }

    fn make_accessor(&self, i: usize, base: syn::Expr) -> syn::Expr {
        syn::ExprIndex {
            attrs: vec![],
            expr: Box::new(base),
            bracket_token: syn::token::Bracket(self.span),
            index: Box::new(
                syn::ExprLit {
                    attrs: vec![],
                    lit: syn::LitInt::new(&i.to_string(), self.span).into(),
                }
                .into(),
            ),
        }
        .into()
    }
}

// FIXME: it sucks that I can't use `repeat(elem).take(*len)`

struct PseudoArrayIter<'a> {
    elem: &'a PseudoElemType,
    rem: usize,
}

impl<'a> Iterator for PseudoArrayIter<'a> {
    type Item = &'a PseudoElemType;

    fn next(&mut self) -> Option<Self::Item> {
        if self.rem == 0 {
            return None;
        }
        self.rem -= 1;

        Some(self.elem)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.rem, Some(self.rem))
    }
}

impl DoubleEndedIterator for PseudoArrayIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next()
    }
}

impl<'a> ExactSizeIterator for PseudoArrayIter<'a> {}

impl Represented for PseudoElemType {
    fn extract(&self, repr_width: usize, repr_expr: syn::Expr) -> syn::Expr {
        let span = repr_expr.span();
        let masked = syn::ExprBinary {
            attrs: vec![],
            left: Box::new(parenthesize(repr_expr)),
            op: syn::BinOp::BitAnd(syn::Token![&](span)),
            right: Box::new(mask(Width::Met(span, repr_width), self.width())),
        };

        match self {
            // (#masked) == 1
            Self::Bool(_) => syn::ExprBinary {
                attrs: vec![],
                left: Box::new(parenthesize(masked)),
                op: syn::BinOp::Eq(syn::Token![==](span)),
                right: Box::new(
                    syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("1", span).into() }.into(),
                ),
            }
            .into(),
            // (#masked) as _
            Self::UInt(..) => syn::ExprCast {
                attrs: vec![],
                expr: Box::new(parenthesize(masked)),
                as_token: syn::Token![as](span),
                ty: Box::new(syn::TypeInfer { underscore_token: syn::Token![_](span) }.into()),
            }
            .into(),
            // unsafe { ::regent::Bitwise::from_repr_unchecked(#masked) }
            Self::ImplBitwise(_) => syn::ExprUnsafe {
                attrs: vec![],
                unsafe_token: syn::Token![unsafe](span),
                block: blockify(syn::ExprCall {
                    attrs: vec![],
                    func: Box::new(expr_path!(span; ::regent::Bitwise::from_repr_unchecked)),
                    paren_token: syn::token::Paren(span),
                    args: once(syn::Expr::from(masked)).collect(),
                }),
            }
            .into(),
        }
    }

    fn extend(&self, _: usize, field_expr: syn::Expr) -> syn::Expr {
        let span = field_expr.span();

        match self {
            // ::regent::Bitwise::into_repr(#field_expr)
            Self::ImplBitwise(_) => syn::ExprCall {
                attrs: vec![],
                func: Box::new(expr_path!(span; ::regent::Bitwise::into_repr)),
                paren_token: syn::token::Paren(span),
                args: once(field_expr).collect(),
            }
            .into(),
            // (#field_expr) as ::regent::Bitwise::Repr
            _ => syn::ExprCast {
                attrs: vec![],
                expr: Box::new(parenthesize(field_expr)),
                as_token: syn::Token![as](span),
                ty: Box::new(ty_path!(span; ::regent::Bitwise::Repr)),
            }
            .into(),
        }
    }
}
