// SPDX-License-Identifier: MPL-2.0

//! Struct fields.

use super::*;

/// Models a struct field.
pub(super) struct Field {
    /// The width of the corresponding bitfield.
    pub(super) width: Width,
    /// The constant value of the corresponding bitfield, if any.
    pub(super) constant: Option<syn::Expr>,
    /// The span.
    pub(super) span: Span2,
    /// The outer attributes.
    pub(super) attrs: Vec<syn::Attribute>,
    /// The visibility.
    pub(super) vis: syn::Visibility,
    /// The name of the field.
    pub(super) ident: syn::Ident,
    /// The API-compatible type of the field.
    pub(super) api_ty: syn::Type,
    /// Produces a [`syn::Expr`] that extracts this field from a struct representation.
    ///
    /// # Arguments
    ///
    /// The first argument is `repr_width` and specifies the bit-width of the struct
    /// representation, and the second is `repr_expr`, the expression for the representation
    /// itself.
    ///
    /// This function expects the field to already occupy the least-significant bits of the
    /// representation (i.e., it has been right-shifted to the position of the field).
    pub(super) extract: ExtractFn,
    /// Produces a [`syn::Expr`] that extends this field into its representation.
    ///
    /// # Arguments
    ///
    /// The first argument is `repr_width` and specifies the bit-width of the struct
    /// representation, and the second is `field_expr`, the expression for the field (that is
    /// to be extended).
    pub(super) extend: ExtendFn,
}

type ExtractFn = Box<dyn Fn(usize, syn::Expr) -> syn::Expr>;
type ExtendFn = Box<dyn Fn(usize, syn::Expr) -> syn::Expr>;

impl Field {
    /// Attempts to parse a `Field` from a [`syn::Field`].
    ///
    /// # Arguments
    ///
    /// `i` is the index of this field. An index of 0 corresponds to the most-significant field, and
    /// each subsequent next most-significant field increments the index by one.
    ///
    /// `field` is the [`syn::Field`]. This function consumes it by-move.
    pub(super) fn parse(i: usize, mut field: syn::Field) -> Result<Self> {
        let span = field.span();

        let pseudo_ty = Type::parse(field.ty)?;
        let width = pseudo_ty.width();
        let (extract, extend) = pseudo_ty.extract_extend();
        let api_ty = {
            let span = pseudo_ty.span();

            pseudo_ty
                .try_into_api_type()
                .ok_or_else(|| err!(span; "this cannot be made into an API type"))?
        };

        let attrs = Attrs::parse(&mut field.attrs)?;
        let constant = attrs.constant;

        let ident = field.ident.unwrap_or_else(|| syn::Ident::new(&format!("f{i}"), span));

        Ok(Self {
            width,
            constant,
            span,
            attrs: field.attrs,
            vis: field.vis,
            ident,
            api_ty,
            extract,
            extend,
        })
    }
}

/// Outer attributes on a struct field that are recognized specially by [`bitwise`].
#[derive(Default)]
struct Attrs {
    /// The value associated with the `#[constant]` attribute, if any.
    constant: Option<syn::Expr>,
}

impl Attrs {
    /// Attempts to parse outer attributes on a struct field.
    ///
    /// # Arguments
    ///
    /// `attrs` is a mutably borrowed vector of [`syn::Attribute`]s. Attributes specific to
    /// [`bitwise`] are parsed and then removed from the vector, and all other attributes are
    /// ignored and left as-is.
    fn parse(attrs: &mut Vec<syn::Attribute>) -> Result<Self> {
        let mut result = Self::default();

        let mut i = 0;
        while i < attrs.len() {
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

                    // This looks like:
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

/// The type of a struct field 'as written'.
///
/// This type is [spanned](Span2). The associated span can be obtained from the [`span`](Self::span)
/// method.
#[derive(Clone)]
enum Type {
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
    /// Attempts to parse a `Type` from a [`syn::Type`].
    fn parse(ty: syn::Type) -> Result<Self> {
        match ty {
            syn::Type::Path(elem) => ElemType::parse(elem).map(Self::Elem),
            syn::Type::Tuple(tuple) => Self::parse_tuple(tuple.span(), tuple.elems),
            syn::Type::Array(array) => Self::parse_array(array.span(), *array.elem, array.len),
            _ => Err(err!(ty.span(); "field type is not supported")),
        }
    }

    /// Parses a tuple type.
    fn parse_tuple(span: Span2, elems: impl IntoIterator<Item = syn::Type>) -> Result<Self> {
        let elems: Vec<ElemType> = elems
            .into_iter()
            .map(|elem| {
                if let syn::Type::Path(elem) = elem {
                    ElemType::parse(elem)
                } else {
                    Err(err!(elem.span(); "tuple element must be a path"))
                }
            })
            .collect::<Result<_>>()?;
        if elems.is_empty() {
            return Err(err!(span; "tuple cannot have zero elements"));
        }

        Ok(Self::Tuple(span, elems))
    }

    /// Parses an array type.
    fn parse_array(span: Span2, elem: syn::Type, len: syn::Expr) -> Result<Self> {
        let syn::Type::Path(elem) = elem else {
            return Err(err!(elem.span(); "array element must be a path"));
        };
        let elem = ElemType::parse(elem)?;
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

        Ok(Self::Array { span, elem, len })
    }

    /// The span of this type.
    fn span(&self) -> Span2 {
        match self {
            Self::Elem(elem) => elem.span(),
            Self::Tuple(span, _) => *span,
            Self::Array { span, .. } => *span,
        }
    }

    /// The bit-width of this type.
    fn width(&self) -> Width {
        match self {
            Self::Elem(elem) => elem.width(),
            Self::Tuple(span, elems) => elems
                .into_iter()
                .fold(Width::Met(*span, 0), |acc, elem| Width::add(acc, elem.width())),
            Self::Array { span, elem, len } => Width::mul(elem.width(), Width::Met(*span, *len)),
        }
    }

    fn try_into_api_type(self) -> Option<syn::Type> {
        match self {
            Self::Elem(elem) => elem.try_into_api_type(),
            Self::Tuple(span, elems) => elems
                .into_iter()
                .map(ElemType::try_into_api_type)
                .collect::<Option<Punctuated<_, _>>>()
                .map(|elems| syn::TypeTuple { paren_token: syn::token::Paren(span), elems }.into()),
            Self::Array { span, elem, len } => elem.try_into_api_type().map(|elem| {
                syn::TypeArray {
                    bracket_token: syn::token::Bracket(span),
                    elem: Box::new(elem.into()),
                    semi_token: syn::Token![;](span),
                    len: syn::ExprLit {
                        attrs: vec![],
                        lit: syn::LitInt::new(&len.to_string(), span).into(),
                    }
                    .into(),
                }
                .into()
            }),
        }
    }
}

/// An inner type in a [tuple](Type::Tuple) or [array](Type::Array).
///
/// This type is [spanned](Span2). The associated span can be obtained from the [`span`](Self::span)
/// method.
#[derive(Clone)]
enum ElemType {
    /// A boolean: `bool`.
    Bool(Span2),
    /// A [`uint::PseudoType`].
    UInt(Span2, uint::PseudoType),
    /// A user-defined type that implements the `Bitwise` trait.
    ImplBitwise(syn::TypePath),
}

impl ElemType {
    /// Attempts to parse an `ElemType` from a [`syn::TypePath`].
    fn parse(ty: syn::TypePath) -> Result<Self> {
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
    fn span(&self) -> Span2 {
        match self {
            Self::Bool(span) => *span,
            Self::UInt(span, _) => *span,
            Self::ImplBitwise(ty) => ty.span(),
        }
    }

    /// The bit-width of this type.
    fn width(&self) -> Width {
        match self {
            Self::Bool(span) => Width::Met(*span, 1),
            Self::UInt(span, ty) => Width::Met(*span, ty.width()),
            Self::ImplBitwise(ty) => Width::Ct({
                let span = ty.span();

                // This looks like:
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

    fn try_into_api_type(self) -> Option<syn::Type> {
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

trait RepresentedExt {
    fn extract_extend(&self) -> (ExtractFn, ExtendFn);
}

impl<T: Represented> RepresentedExt for T {
    fn extract_extend(&self) -> (ExtractFn, ExtendFn) {
        todo!()
    }
}

/// Types backed by an integral representation.
trait Represented {
    fn extract(&self, repr_width: usize, repr_expr: syn::Expr) -> syn::Expr;

    fn extend(&self, repr_width: usize, field_expr: syn::Expr) -> syn::Expr;
}

impl Represented for Type {
    fn extract(&self, repr_width: usize, repr_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Elem(elem) => elem.extract(repr_width, repr_expr),
            Self::Tuple(span, elems) => Self::extract_container(
                repr_width,
                repr_expr,
                elems.iter(),
                |elems| {
                    syn::ExprTuple { attrs: vec![], paren_token: syn::token::Paren(*span), elems }
                        .into()
                },
                |expr, i| {
                    syn::ExprField {
                        attrs: vec![],
                        base: Box::new(expr),
                        dot_token: syn::Token![.](*span),
                        member: syn::Member::Unnamed(i.into()),
                    }
                    .into()
                },
            ),
            Self::Array { span, elem, len } => Self::extract_container(
                repr_width,
                repr_expr,
                {
                    // FIXME: it sucks that I can't use `repeat(elem).take(*len)`

                    struct Iter<'a> {
                        elem: &'a ElemType,
                        rem: usize,
                    }

                    impl<'a> Iterator for Iter<'a> {
                        type Item = &'a ElemType;

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

                    impl DoubleEndedIterator for Iter<'_> {
                        fn next_back(&mut self) -> Option<Self::Item> {
                            self.next()
                        }
                    }

                    impl<'a> ExactSizeIterator for Iter<'a> {}

                    Iter { elem, rem: *len }
                },
                |elems| {
                    syn::ExprArray {
                        attrs: vec![],
                        bracket_token: syn::token::Bracket(*span),
                        elems,
                    }
                    .into()
                },
                |expr, i| {
                    syn::ExprIndex {
                        attrs: vec![],
                        expr: Box::new(expr),
                        bracket_token: syn::token::Bracket(*span),
                        index: Box::new(
                            syn::ExprLit {
                                attrs: vec![],
                                lit: syn::LitInt::new(&i.to_string(), *span).into(),
                            }
                            .into(),
                        ),
                    }
                    .into()
                },
            ),
        }
    }

    fn extend(&self, repr_width: usize, field_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Elem(elem) => elem.extend(repr_width, field_expr),
            Self::Tuple(span, elems) => Self::extend_container(repr_width, field_expr),
            Self::Array { span, elem, len } => Self::extend_container(repr_width, field_expr),
        }
    }
}

impl Type {
    fn extract_container<'a, Elems>(
        repr_width: usize,
        repr_expr: syn::Expr,
        elems: Elems,
        make_container: impl Fn(Punctuated<syn::Expr, syn::Token![,]>) -> syn::Expr,
        make_accessor: impl Fn(syn::Expr, usize) -> syn::Expr,
    ) -> syn::Expr
    where
        Elems: Iterator<Item = &'a ElemType>,
        Elems: DoubleEndedIterator,
    {
        let span = repr_expr.span();

        // let mut repr = #repr_expr;
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

        let tmp_elems: Punctuated<_, _> = elems
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
                            None,
                        ),
                        syn::Stmt::Expr(expr_path!(span; it), None),
                    ],
                },
            })
            .map(syn::Expr::from)
            .collect();
        let elems =
            (0..tmp_elems.len()).rev().map(|i| make_accessor(expr_path!(span; tmp), i)).collect();

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
                expr: Box::new(make_container(tmp_elems)),
                diverge: None,
            }),
            semi_token: syn::Token![;](span),
        });
        let elems = syn::Stmt::Expr(make_container(elems), None);

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

    fn extend_container(repr_width: usize, field_expr: syn::Expr) -> syn::Expr {
        todo!()
    }
}

impl Represented for ElemType {
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

/// Creates a bit-mask of the form:
///
/// ```no_run
/// (!0 >> (#repr_width - #width))
/// ```
fn mask(repr_width: Width, width: Width) -> syn::Expr {
    let span = width.span();

    let lhs = syn::ExprUnary {
        attrs: vec![],
        op: syn::UnOp::Not(syn::Token![!](span)),
        expr: Box::new(
            syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("0", span).into() }.into(),
        ),
    }
    .into();
    let rhs = parenthesize(syn::ExprBinary {
        attrs: vec![],
        left: Box::new(repr_width.parenthesize().into()),
        op: syn::BinOp::Sub(syn::Token![-](span)),
        right: Box::new(width.parenthesize().into()),
    });

    parenthesize(syn::ExprBinary {
        attrs: vec![],
        left: Box::new(lhs),
        op: syn::BinOp::Shr(syn::Token![>>](span)),
        right: Box::new(rhs),
    })
}
