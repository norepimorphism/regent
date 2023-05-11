// SPDX-License-Identifier: MPL-2.0

use super::*;

pub(super) trait HasRepr {
    /// Produces a value of this type from a representation.
    fn decode(&self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr;

    /// Produces a representation of this type from a value.
    fn encode(&self, repr_width: Width, value_exprs: syn::Expr) -> syn::Expr;
}

impl HasRepr for field::Type {
    fn decode(&self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Elem(ty) => ty.decode(repr_width, repr_expr),
            _ => unsafe { self.decode_container(repr_width, repr_expr) },
        }
    }

    fn encode(&self, repr_width: Width, value_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Elem(ty) => ty.encode(repr_width, value_expr),
            _ => unsafe { self.encode_container(repr_width, value_expr) },
        }
    }
}

impl field::Type {
    unsafe fn decode_container(&self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr {
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

        // The strategy for container types is to create a temporary container formed from
        // block expressions that continuously bit-shift the next element to the bottom of
        // `repr` and then feed those elements, in reverse order, to another container.
        // Reversal is necessary because we take from the least-significant bits of `repr`,
        // which represent the current last element.

        // This closure produces a `syn::Block` that extracts the next element from a container type
        // (i.e., tuple or array).
        let get_elem_block = |elem_ty: &field::ElemType| {
            let elem_width = elem_ty.width();

            // {
            //     let elem = /* decoded value from #repr_expr */;
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
                            ident: elem_ident,
                            subpat: None,
                        }
                        .into(),
                        init: Some(syn::LocalInit {
                            eq_token,
                            expr: Box::new(elem_ty.decode(elem_width, repr_expr.clone())),
                            diverge: None,
                        }),
                        semi_token,
                    }),
                    syn::Stmt::Expr(
                        syn::ExprBinary {
                            attrs: vec![],
                            left: Box::new(repr_expr),
                            op: syn::BinOp::ShrAssign(syn::Token![>>=](span)),
                            right: Box::new(elem_width.into_expr()),
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
        let make_tmp_local_and_elems_expr =
            |elem_tys: &(dyn DoubleEndedIterator
                   + ExactSizeIterator
                   + Iterator<Item = field::ElemType>),
             get_elem_expr: fn(&field::ElemType) -> syn::Expr,
             make_accessor: fn(usize) -> syn::Expr,
             make_container: fn(Elements) -> syn::Expr| {
                let (tmp_elems, elems): (Elements, Elements) = (*elem_tys)
                    .enumerate()
                    .rev()
                    .map(|(i, elem_ty)| (get_elem_expr(elem_ty), make_accessor(i)))
                    .unzip();
                // let tmp = (#get_elem_block, #get_elem_block, ...);
                let tmp_local = syn::Local {
                    attrs: vec![],
                    let_token,
                    pat: syn::PatIdent {
                        attrs: vec![],
                        by_ref: None,
                        mutability: None,
                        ident: tmp_ident,
                        subpat: None,
                    }
                    .into(),
                    init: Some(syn::LocalInit {
                        eq_token,
                        expr: Box::new(make_container(tmp_elems)),
                        diverge: None,
                    }),
                    semi_token,
                };
                let elems_expr = make_container(elems);

                (tmp_local, elems_expr)
            };

        match self {
            Self::Elem(_) => std::hint::unreachable_unchecked(),
            Self::Tuple(elem_tys) => {
                let (tmp_local, elems_expr) = make_tmp_local_and_elems_expr(
                    elem_tys,
                    // #get_elem_block
                    |elem_ty| {
                        syn::ExprBlock {
                            attrs: vec![],
                            label: None,
                            block: get_elem_block(elem_ty),
                        }
                        .into()
                    },
                    |i| {
                        // tmp.#i
                        syn::ExprField {
                            attrs: vec![],
                            base: Box::new(
                                syn::ExprPath {
                                    attrs: vec![],
                                    qself: None,
                                    path: tmp_ident.into(),
                                }
                                .into(),
                            ),
                            dot_token,
                            member: syn::Member::Unnamed(i.into()),
                        }
                        .into()
                    },
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
            Self::Array { ty: elem_ty, len } => {
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
                                        block: get_elem_block(elem_ty),
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
                    &repeat(elem_ty).take(*len),
                    // get_elem()
                    |elem_ty| {
                        syn::ExprCall {
                            attrs: vec![],
                            func: Box::new(
                                syn::ExprPath {
                                    attrs: vec![],
                                    qself: None,
                                    path: get_elem_ident.into(),
                                }
                                .into(),
                            ),
                            paren_token,
                            args: Punctuated::new(),
                        }
                        .into()
                    },
                    |i| {
                        // tmp.#i
                        syn::ExprIndex {
                            attrs: vec![],
                            expr: Box::new(
                                syn::ExprPath {
                                    attrs: vec![],
                                    qself: None,
                                    path: tmp_ident.into(),
                                }
                                .into(),
                            ),
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

    unsafe fn encode_container(&self, repr_width: Width, value_expr: syn::Expr) -> syn::Expr {
        let span = value_expr.span();

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
        let or_token = syn::Token![|](span);
        let paren_token = syn::token::Paren(span);
        let semi_token = syn::Token![;](span);

        // repr
        let repr_expr = expr_path!(repr_ident);
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
        // This closure generates a set of statements that collectively set the next element
        // in a container type (i.e., tuple or array).
        let set_elem_stmts = |elem_ty: &field::ElemType, elem_expr| {
            let make_stmt = |op, right| {
                syn::Stmt::Expr(
                    syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(repr_expr),
                        op,
                        right: Box::new(right),
                    }
                    .into(),
                    Some(semi_token),
                )
            };

            // repr <<= #elem_width;
            // repr |= /* encoded value of #elem_expr */;
            [
                make_stmt(
                    syn::BinOp::ShlAssign(syn::Token![<<=](span)),
                    elem_ty.width().into_expr().into(),
                ),
                make_stmt(
                    syn::BinOp::BitOrAssign(syn::Token![|=](span)),
                    elem_ty.encode(repr_width, elem_expr),
                ),
            ]
        };

        match self {
            Self::Elem(_) => std::hint::unreachable_unchecked(),
            Self::Tuple(tys) => {
                // #repr_local
                // #set_elem_stmts
                // #set_elem_stmts
                // /* ... */
                // #repr_expr
                let stmts = once(syn::Stmt::Local(repr_local))
                    .chain({
                        tys.iter()
                            .enumerate()
                            .map(|(i, elem_ty)| {
                                // #value_expr.#i
                                let elem_expr = syn::ExprField {
                                    attrs: vec![],
                                    base: Box::new(value_expr),
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
            Self::Array { ty: elem_ty, len } => {
                let i_ident = syn::Ident::new("i", span);
                // #value_expr[i]
                let elem_expr = syn::ExprIndex {
                    attrs: vec![],
                    expr: Box::new(value_expr),
                    bracket_token,
                    index: Box::new(
                        syn::ExprPath { attrs: vec![], qself: None, path: i_ident.into() }.into(),
                    ),
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
                    body: syn::Block {
                        brace_token,
                        stmts: set_elem_stmts(elem_ty, elem_expr).into_iter().collect(),
                    },
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

impl HasRepr for PrimeType {
    fn decode(&self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr {
        let span = repr_expr.span();
        let inner = syn::ExprBinary {
            attrs: vec![],
            left: Box::new(repr_expr),
            op: syn::BinOp::BitAnd(syn::Token![&](span)),
            right: Box::new(repr_width.into_mask(repr_width).into()),
        }
        .into();

        match self {
            // #inner == 1
            Self::Bool => syn::ExprBinary {
                attrs: vec![],
                left: Box::new(inner),
                op: syn::BinOp::Eq(syn::Token![==](span)),
                right: Box::new(
                    syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("1", span).into() }.into(),
                ),
            }
            .into(),
            // #inner as _
            Self::UInt(_) => syn::ExprCast {
                attrs: vec![],
                expr: Box::new(inner),
                as_token: syn::Token![as](span),
                ty: Box::new(syn::TypeInfer { underscore_token: syn::Token![_](span) }.into()),
            }
            .into(),
            // unsafe { ::regent::Bitwise::from_repr_unchecked(#inner) }
            Self::Other(_) => syn::ExprUnsafe {
                attrs: vec![],
                unsafe_token: syn::Token![unsafe](span),
                block: syn::Block {
                    brace_token: syn::token::Brace(span),
                    stmts: vec![syn::Stmt::Expr(
                        syn::ExprCall {
                            attrs: vec![],
                            func: Box::new(
                                syn::ExprPath {
                                    attrs: vec![],
                                    qself: None,
                                    path: syn::Path {
                                        leading_colon: Some(syn::Token![::](span)),
                                        segments: ["regent", "Bitwise", "from_repr_unchecked"]
                                            .into_iter()
                                            .collect(),
                                    },
                                }
                                .into(),
                            ),
                            paren_token: syn::token::Paren(span),
                            args: [inner].into_iter().collect(),
                        }
                        .into(),
                        None,
                    )],
                },
            }
            .into(),
        }
    }

    fn encode(&self, repr_width: Width, value_expr: syn::Expr) -> syn::Expr {
        let span = value_expr.span();

        syn::ExprBinary {
            attrs: vec![],
            left: Box::new(match self {
                // ::regent::Bitwise::to_repr(#value_expr)
                Self::Other(_) => syn::ExprCall {
                    attrs: vec![],
                    func: Box::new(
                        syn::ExprPath {
                            attrs: vec![],
                            qself: None,
                            path: syn::Path {
                                leading_colon: Some(syn::Token![::](span)),
                                segments: ["regent", "Bitwise", "to_repr"].into_iter().collect(),
                            },
                        }
                        .into(),
                    ),
                    paren_token: syn::token::Paren(span),
                    args: [value_expr].into_iter().collect(),
                }
                .into(),
                // #value_expr as ItemRepr
                _ => syn::ExprCast {
                    attrs: vec![],
                    expr: Box::new(value_expr),
                    as_token: syn::Token![as](span),
                    ty: Box::new(syn::ExprPath::from(syn::Ident::new("ItemRepr", span)).into()),
                }
                .into(),
            }),
            op: syn::BinOp::BitAnd(syn::Token![&](span)),
            right: Box::new(repr_width.into_mask(repr_width).into()),
        }
        .into()
    }
}
