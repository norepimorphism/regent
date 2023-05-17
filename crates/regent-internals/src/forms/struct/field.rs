// SPDX-License-Identifier: MPL-2.0

//! Struct fields.

use super::*;

/// Outer attributes on a struct field that are recognized specially by [`bitwise`].
#[derive(Default)]
pub(super) struct Attrs {
    /// The value associated with the `#[constant]` attribute, if any.
    pub(super) constant: Option<syn::Expr>,
}

impl Attrs {
    /// Parses outer attributes on a struct field.
    ///
    /// # Arguments
    ///
    /// `attrs` is a mutably borrowed vector of [`syn::Attribute`]s. Attributes specific to
    /// [`bitwise`] are parsed and then removed from the vector, and all other attributes are
    /// ignored and left as-is.
    pub(super) fn parse(attrs: &mut Vec<syn::Attribute>) -> Result<Self, Error> {
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

/// The type of a struct field.
///
/// This type is [spanned](Span2). The associated span can be obtained from the [`span`](Self::span)
/// method.
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

    /// Parses a tuple type.
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

    /// Parses an array type.
    fn parse_array(span: Span2, elem: syn::Type, len: syn::Expr) -> Result<Self, Error> {
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
    pub(super) fn span(&self) -> Span2 {
        match self {
            Self::Elem(elem) => elem.span(),
            Self::Tuple(span, _) => *span,
            Self::Array { span, .. } => *span,
        }
    }

    /// The bit-width of this type.
    pub(super) fn width(&self) -> Width {
        match self {
            Self::Elem(elem) => elem.width(),
            Self::Tuple(span, elems) => elems
                .into_iter()
                .fold(Width::Met(*span, 0), |acc, elem| Width::add(acc, elem.width())),
            Self::Array { span, elem, len } => Width::mul(elem.width(), Width::Met(*span, *len)),
        }
    }

    pub(super) fn try_into_api_type(self) -> Option<syn::Type> {
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

    pub(super) fn try_into_api_type(self) -> Option<syn::Type> {
        match self {
            Self::Bool(span) => Some(type_path!(span; bool)),
            Self::UInt(span, mut ty) => {
                ty.round_up();
                let ty = ty.try_into_rust_type()?;

                Some(ty.into_syn_type(span))
            }
            Self::ImplBitwise(ty) => Some(ty.into()),
        }
    }
}

/// Types backed by an integral representation.
pub(super) trait Represented {
    /// Produces a [`syn::Expr`] to extract a value of this type from a representation.
    ///
    /// # Arguments
    ///
    /// `repr_width` is the bit-width of the representation. `repr_expr` is an expression that
    /// expands to the value of the representation.
    fn make_extract_expr(self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr;

    /// Produces a [`syn::Expr`] to extend a value of this type into its representation.
    ///
    /// # Arguments
    ///
    /// `repr_width` is the bit-width of the representation. `ty_expr` is an expression that expands
    /// to the value of this type.
    fn make_extend_expr(self, repr_width: Width, ty_expr: syn::Expr) -> syn::Expr;
}

impl Represented for field::Type {
    fn make_extract_expr(self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Elem(ty) => ty.make_extract_expr(repr_width, repr_expr),
            _ => unsafe { self.make_extract_container_expr(repr_width, repr_expr) },
        }
    }

    fn make_extend_expr(self, repr_width: Width, ty_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Elem(ty) => ty.make_extend_expr(repr_width, ty_expr),
            _ => unsafe { self.make_extend_container_expr(repr_width, ty_expr) },
        }
    }
}

impl field::Type {
    /// [`Represented::make_extract_expr`] for container types (tuple and array) only.
    unsafe fn make_extract_container_expr(self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr {
        let span = repr_expr.span();

        // Common identifiers.
        let elem_ident = syn::Ident::new("elem", span);
        let get_elem_ident = syn::Ident::new("get_elem", span);
        let tmp_ident = syn::Ident::new("tmp", span);
        // Common tokens.
        let brace_token = syn::token::Brace(span);
        let bracket_token = syn::token::Bracket(span);
        let dot_token = syn::Token![.](span);
        let eq_token = syn::Token![=](span);
        let let_token = syn::Token![let](span);
        let or_token = syn::Token![|](span);
        let paren_token = syn::token::Paren(span);
        let semi_token = syn::Token![;](span);

        // The strategy is to create a temporary container, formed from block expressions that
        // continuously bit-shift the next element to the bottom of `repr`, and then feed those
        // elements, in reverse order, to another container. Reversal is necessary because we take
        // from the least-significant bits of `repr`, which represent the current last element.

        // This closure produces a `syn::Block` that extracts the next element from a container
        // type.
        let get_elem_block = |elem: &field::ElemType| {
            let elem_width = elem.width();

            // {
            //     let elem = /* extracted value from #repr_expr */;
            //     #repr_expr >>= #elem_width;
            //
            //     elem
            // }
            syn::Block {
                brace_token,
                stmts: vec![
                    syn::Stmt::Local(syn::Local {
                        attrs: vec![],
                        let_token,
                        pat: syn::PatIdent {
                            attrs: vec![],
                            by_ref: None,
                            mutability: None,
                            ident: elem_ident.clone(),
                            subpat: None,
                        }
                        .into(),
                        init: Some(syn::LocalInit {
                            eq_token,
                            expr: Box::new(elem.make_extract_expr(repr_width, repr_expr.clone())),
                            diverge: None,
                        }),
                        semi_token,
                    }),
                    syn::Stmt::Expr(
                        syn::ExprBinary {
                            attrs: vec![],
                            left: Box::new(repr_expr),
                            op: syn::BinOp::ShrAssign(syn::Token![>>=](span)),
                            right: Box::new(elem_width.into_expr::<false>()),
                        }
                        .into(),
                        Some(semi_token),
                    ),
                    syn::Stmt::Expr(expr_path!(elem_ident), None),
                ],
            }
        };
        type Elements = Punctuated<syn::Expr, syn::Token![,]>;
        // This closure produces a 2-tuple containing the local variable representing the
        // temporary container and an expression that evaluates to the final container, in
        // that order.
        fn make_tmp_local_and_elems_expr<Elems>(
            span: Span2,
            tmp_ident: syn::Ident,
            elems: Elems,
            get_elem_expr: impl Fn(&field::ElemType) -> syn::Expr,
            make_accessor: impl Fn(usize) -> syn::Expr,
            make_container: impl Fn(Elements) -> syn::Expr,
        ) -> (syn::Local, syn::Expr)
        where
            Elems: ExactSizeIterator + DoubleEndedIterator,
            Elems: Iterator<Item = field::ElemType>,
        {
            let (tmp_elems, elems): (Elements, Elements) = elems
                .enumerate()
                .rev()
                .map(|(i, elem)| (get_elem_expr(elem), make_accessor(i)))
                .unzip();
            // let tmp = /* container */;
            let tmp_local = syn::Local {
                attrs: vec![],
                let_token: syn::Token![let](span),
                pat: syn::PatIdent {
                    attrs: vec![],
                    by_ref: None,
                    mutability: None,
                    ident: tmp_ident,
                    subpat: None,
                }
                .into(),
                init: Some(syn::LocalInit {
                    eq_token: syn::Token![=](span),
                    expr: Box::new(make_container(tmp_elems)),
                    diverge: None,
                }),
                semi_token: syn::Token![;](span),
            };
            let elems_expr = make_container(elems);

            (tmp_local, elems_expr)
        }

        match self {
            Self::Elem(_) => std::hint::unreachable_unchecked(),
            Self::Tuple(_, elems) => {
                let (tmp_local, elems_expr) = make_tmp_local_and_elems_expr(
                    span,
                    tmp_ident.clone(),
                    elems.into_iter(),
                    |elem| {
                        syn::ExprBlock { attrs: vec![], label: None, block: get_elem_block(elem) }
                            .into()
                    },
                    // tmp.#i
                    |i| syn::ExprField {
                        attrs: vec![],
                        base: Box::new(expr_path!(tmp_ident)),
                        dot_token,
                        member: syn::Member::Unnamed(i.into()),
                    }
                    .into(),
                    |elems| syn::ExprTuple { attrs: vec![], paren_token, elems }.into(),
                );

                syn::ExprBlock {
                    attrs: vec![],
                    label: None,
                    block: syn::Block {
                        brace_token,
                        stmts: vec![syn::Stmt::Local(tmp_local), syn::Stmt::Expr(elems_expr, None)],
                    },
                }
                .into()
            }
            Self::Array { span, elem, .. } => {
                // let get_elem = || #get_elem_block;
                let get_elem_local = syn::Local {
                    attrs: vec![],
                    let_token,
                    pat: syn::PatIdent {
                        attrs: vec![],
                        by_ref: None,
                        mutability: None,
                        ident: get_elem_ident,
                        subpat: None,
                    }
                    .into(),
                    init: Some(syn::LocalInit {
                        eq_token,
                        expr: Box::new(
                            syn::ExprClosure {
                                attrs: vec![],
                                lifetimes: None,
                                constness: None,
                                movability: None,
                                asyncness: None,
                                capture: None,
                                or1_token: or_token,
                                inputs: Punctuated::new(),
                                or2_token: or_token,
                                output: syn::ReturnType::Default,
                                body: Box::new(
                                    syn::ExprBlock {
                                        attrs: vec![],
                                        label: None,
                                        block: get_elem_block(elem),
                                    }
                                    .into(),
                                ),
                            }
                            .into(),
                        ),
                        diverge: None,
                    }),
                    semi_token,
                };
                let (tmp_local, elems_expr) = make_tmp_local_and_elems_expr(
                    span,
                    tmp_ident.clone(),
                    once(elem),
                    // get_elem()
                    |elem_ty| syn::ExprCall {
                        attrs: vec![],
                        func: Box::new(expr_path!(get_elem_ident)),
                        paren_token,
                        args: Punctuated::new(),
                    }
                    .into(),
                    |i| {
                        // tmp.#i
                        syn::ExprIndex {
                            attrs: vec![],
                            expr: Box::new(expr_path!(tmp_ident)),
                            bracket_token,
                            index: Box::new(
                                syn::ExprLit {
                                    attrs: vec![],
                                    // FIXME: span
                                    lit: syn::LitInt::new(&i.to_string(), Span2::call_site())
                                        .into(),
                                }
                                .into(),
                            ),
                        }
                        .into()
                    },
                    |elems| syn::ExprArray { attrs: vec![], bracket_token, elems }.into(),
                );

                // #get_elem_local
                // #tmp_local
                // #elems_expr
                syn::ExprBlock {
                    attrs: vec![],
                    label: None,
                    block: syn::Block {
                        brace_token,
                        stmts: vec![
                            syn::Stmt::Local(get_elem_local),
                            syn::Stmt::Local(tmp_local),
                            syn::Stmt::Expr(elems_expr, None),
                        ],
                    },
                }
                .into()
            }
        }
    }

    /// [`Represented::make_extend_expr`] for container types (tuple and array) only.
    unsafe fn make_extend_container_expr(self, repr_width: Width, ty_expr: syn::Expr) -> syn::Expr {
        let span = ty_expr.span();

        // Common identifiers.
        let repr_ident = syn::Ident::new("repr", span);
        // Common tokens.
        let brace_token = syn::token::Brace(span);
        let bracket_token = syn::token::Bracket(span);
        let dot_dot_token = syn::Token![..](span);
        let eq_token = syn::Token![=](span);
        let for_token = syn::Token![for](span);
        let in_token = syn::Token![in](span);
        let let_token = syn::Token![let](span);
        let semi_token = syn::Token![;](span);

        // repr
        let repr_expr: syn::Expr = expr_path!(repr_ident.clone());
        // let repr = 0;
        let repr_local = syn::Local {
            attrs: vec![],
            let_token,
            pat: syn::PatIdent {
                attrs: vec![],
                by_ref: None,
                mutability: None,
                ident: repr_ident,
                subpat: None,
            }
            .into(),
            init: Some(syn::LocalInit {
                eq_token,
                expr: Box::new(
                    syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("0", span).into() }.into(),
                ),
                diverge: None,
            }),
            semi_token,
        };
        // This closure generates a set of statements that collectively set the next element in a
        // container type.
        let set_elem_stmts = |elem: field::ElemType, elem_expr| {
            let make_stmt = |op, rhs: syn::Expr| {
                syn::Stmt::Expr(
                    syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(repr_expr.clone()),
                        op,
                        right: Box::new(rhs),
                    }
                    .into(),
                    Some(semi_token),
                )
            };

            // repr <<= #elem_width;
            // repr |= /* extended value of #elem_expr */;
            [
                make_stmt(
                    syn::BinOp::ShlAssign(syn::Token![<<=](span)),
                    elem.clone().width().into_expr::<false>(),
                ),
                make_stmt(
                    syn::BinOp::BitOrAssign(syn::Token![|=](span)),
                    elem.make_extend_expr(repr_width, elem_expr),
                ),
            ]
        };

        match self {
            Self::Elem(_) => std::hint::unreachable_unchecked(),
            Self::Tuple(span, elems) => {
                // #repr_local
                // #set_elem_stmts
                // #set_elem_stmts
                // /* ... */
                // #repr_expr
                let stmts = once(syn::Stmt::Local(repr_local))
                    .chain({
                        elems
                            .into_iter()
                            .enumerate()
                            .map(|(i, elem_ty)| {
                                // #ty_expr.#i
                                let elem_expr = syn::ExprField {
                                    attrs: vec![],
                                    base: Box::new(ty_expr.clone()),
                                    dot_token: syn::Token![.](span),
                                    member: syn::Member::Unnamed(i.into()),
                                }
                                .into();

                                set_elem_stmts(elem_ty, elem_expr)
                            })
                            .flatten()
                    })
                    .chain(once(syn::Stmt::Expr(repr_expr, None)))
                    .collect();

                syn::ExprBlock {
                    attrs: vec![],
                    label: None,
                    block: syn::Block { brace_token, stmts },
                }
                .into()
            }
            Self::Array { span, elem, len } => {
                let i_ident = syn::Ident::new("i", span);
                // #ty_expr[i]
                let elem_expr = syn::ExprIndex {
                    attrs: vec![],
                    expr: Box::new(ty_expr),
                    bracket_token,
                    index: Box::new(expr_path!(i_ident.clone())),
                }
                .into();
                // for i in ..#len {
                //     #set_elem_stmts
                // }
                let for_loop = syn::ExprForLoop {
                    attrs: vec![],
                    label: None,
                    for_token,
                    pat: Box::new(
                        syn::PatIdent {
                            attrs: vec![],
                            by_ref: None,
                            mutability: None,
                            ident: i_ident,
                            subpat: None,
                        }
                        .into(),
                    ),
                    in_token,
                    expr: Box::new(
                        syn::ExprRange {
                            attrs: vec![],
                            start: None,
                            limits: syn::RangeLimits::HalfOpen(dot_dot_token),
                            end: Some(Box::new(
                                syn::ExprLit {
                                    attrs: vec![],
                                    lit: syn::LitInt::new(&len.to_string(), span).into(),
                                }
                                .into(),
                            )),
                        }
                        .into(),
                    ),
                    body: syn::Block { brace_token, stmts: set_elem_stmts(elem, elem_expr).into() },
                }
                .into();
                let stmts = vec![
                    syn::Stmt::Local(repr_local),
                    syn::Stmt::Expr(for_loop, None),
                    syn::Stmt::Expr(repr_expr, None),
                ];

                syn::ExprBlock {
                    attrs: vec![],
                    label: None,
                    block: syn::Block { brace_token, stmts },
                }
                .into()
            }
        }
    }
}

impl Represented for ElemType {
    fn make_extract_expr(self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr {
        let span = repr_expr.span();
        let masked = syn::ExprBinary {
            attrs: vec![],
            left: Box::new(repr_expr),
            op: syn::BinOp::BitAnd(syn::Token![&](span)),
            right: Box::new(mask(repr_width, self.width())),
        }
        .into();

        match self {
            // #masked == 1
            Self::Bool(_) => syn::ExprBinary {
                attrs: vec![],
                left: Box::new(masked),
                op: syn::BinOp::Eq(syn::Token![==](span)),
                right: Box::new(
                    syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("1", span).into() }.into(),
                ),
            }
            .into(),
            // #masked as _
            Self::UInt(..) => syn::ExprCast {
                attrs: vec![],
                expr: Box::new(masked),
                as_token: syn::Token![as](span),
                ty: Box::new(syn::TypeInfer { underscore_token: syn::Token![_](span) }.into()),
            }
            .into(),
            // unsafe { ::regent::Bitwise::from_repr_unchecked(#masked) }
            Self::ImplBitwise(_) => {
                let call_expr = syn::ExprCall {
                    attrs: vec![],
                    func: Box::new(expr_path!(span; ::regent::Bitwise::from_repr_unchecked)),
                    paren_token: syn::token::Paren(span),
                    args: once(masked).collect(),
                }
                .into();

                syn::ExprUnsafe {
                    attrs: vec![],
                    unsafe_token: syn::Token![unsafe](span),
                    block: syn::Block {
                        brace_token: syn::token::Brace(span),
                        stmts: vec![syn::Stmt::Expr(call_expr, None)],
                    },
                }
                .into()
            }
        }
    }

    fn make_extend_expr(self, repr_width: Width, ty_expr: syn::Expr) -> syn::Expr {
        let span = ty_expr.span();
        let lhs = match self {
            // ::regent::Bitwise::into_repr(#ty_expr)
            Self::ImplBitwise(_) => syn::ExprCall {
                attrs: vec![],
                func: Box::new(expr_path!(span; ::regent::Bitwise::into_repr)),
                paren_token: syn::token::Paren(span),
                args: once(ty_expr).collect(),
            }
            .into(),
            // #ty_expr as ::regent::Bitwise::Repr
            _ => syn::ExprCast {
                attrs: vec![],
                expr: Box::new(ty_expr),
                as_token: syn::Token![as](span),
                ty: Box::new(type_path!(span; ::regent::Bitwise::Repr)),
            }
            .into(),
        };
        let rhs = mask(repr_width, self.width());

        syn::ExprBinary {
            attrs: vec![],
            left: Box::new(lhs),
            op: syn::BinOp::BitAnd(syn::Token![&](span)),
            right: Box::new(rhs),
        }
        .into()
    }
}

/// Creates a [`syn::Expr`] that masks the least-significant bits of an expression.
///
/// The expression is of the form:
///
/// ```no_run
/// (!0 >> (#repr_width - #width))
/// ```
fn mask(repr_width: Width, width: Width) -> syn::Expr {
    let span = width.span();
    let parenthesize = |expr| syn::ExprParen {
        attrs: vec![],
        paren_token: syn::token::Paren(span),
        expr: Box::new(expr),
    }
    .into();

    let lhs = syn::ExprUnary {
        attrs: vec![],
        op: syn::UnOp::Not(syn::Token![!](span)),
        expr: Box::new(syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("0", span).into() }.into()),
    }
    .into();
    let rhs = parenthesize(
        syn::ExprBinary {
            attrs: vec![],
            left: Box::new(repr_width.into_expr::<true>()),
            op: syn::BinOp::Sub(syn::Token![-](span)),
            right: Box::new(width.into_expr::<true>()),
        }
        .into()
    );

    parenthesize(
        syn::ExprBinary {
            attrs: vec![],
            left: Box::new(lhs),
            op: syn::BinOp::Shr(syn::Token![>>](span)),
            right: Box::new(rhs),
        }
        .into()
    )
}
