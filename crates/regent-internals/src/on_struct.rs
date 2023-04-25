// SPDX-License-Identifier: MPL-2.0

use std::iter::{once, repeat};

use proc_macro::TokenStream;
use proc_macro2::{Span as Span2, TokenStream as TokenStream2};
use syn::{punctuated::Punctuated, spanned::Spanned as _};

use crate::{EnforceItemWidthStrategy, Error, UIntType};

/// The bit-width of a type known to [`bitwise`].
type Width = crate::ConstUsizeExpr;

/// [`bitwise`](crate::bitwise) for structs.
pub fn bitwise(expected_width: Option<usize>, item: syn::ItemStruct) -> TokenStream {
    crate::check_generics(item.generics);
    let item_span = item.span();
    let syn::ItemStruct {
        attrs: mut item_attrs,
        fields: item_fields,
        ident: item_ident,
        struct_token: item_struct,
        vis: item_vis,
        ..
    } = item;

    // These next few variables are default-initialized for now and will be continuously updated
    // during field processing.

    // This is the total bit-width of all fields.
    let mut item_width = Width::zero(item_span);
    // This is the list of `impl #item_ident` methods we emit.
    let mut item_methods = Vec::new();
    // This is the list of all arguments accepted by `#item_ident::new`.
    let mut item_new_args = Vec::new();
    // This is a list of 'snippets' (or series of statements) that initialize the fields in
    // `#item_ident::new`.
    let mut item_new_stmts = Vec::new();
    // FIXME: name is inconsistent
    let mut from_repr_checked_body = TokenStream2::new();

    // Process fields.
    for (i, field) in item_fields.into_iter().enumerate() {
        let field_span = field.span();
        let syn::Field {
            attrs: field_attrs, ident: field_ident, ty: field_ty, vis: field_vis, ..
        } = field;

        let (field_getter_ident, field_setter_ident) = match field_ident {
            Some(it) => (it.clone(), syn::Ident::new(&format!("set_{it}"), it.span())),
            None => (
                syn::Ident::new(&format!("_{i}"), item_span),
                syn::Ident::new(&format!("set_{i}"), item_span),
            ),
        };
        let field_ident = &field_getter_ident;

        let field_ty = unwrap!(Type::parse(field_span, field_ty).map_err(TokenStream::from));
        unwrap!(field_ty.validate(field_span).map_err(TokenStream::from));

        // This is the position of the least-significant bit of this field.
        let field_offset = item_width.clone();
        // This is the exact width of this field.
        let field_width = field_ty.width();
        item_width += &field_width;

        let field_ty = field_ty.as_rust_primitives();
        if !field_ty.exists() {
            return err!(
                field_span;
                "'bitwise' field cannot be represented in terms of primitive Rust types"
            )
            .into();
        }

        let mut field_value = None;
        for attr in field_attrs {
            // FIXME: don't unwrap.
            let metas = darling::util::parse_attribute_to_meta_list(&attr).unwrap();
            if metas.path.is_ident("constant") {
                #[derive(darling::FromMeta)]
                struct ConstantArgs {
                    value: Option<syn::Expr>,
                }

                let nested_metas: Vec<_> = metas.nested.into_iter().collect();
                // FIXME: don't unwrap.
                let args = ConstantArgs::from_list(&nested_metas).unwrap();
                field_value = Some(match args.value {
                    Some(it) => it.into_token_stream(),
                    None => quote!(<#field_ty as ::core::default::Default>::default()),
                });
            } else {
                return err!(field_span; "invalid attribute").into();
            }
        }

        let new_glue: syn::Expr;
        if let Some(field_value) = field_value {
            // This is the simple case for constant fields only. We don't need to generate getters
            // or setters.

            let field_decoded = field_ty.decode(quote!(repr), &field_width);
            from_repr_checked_body.extend(quote!({
                let repr: ItemRepr = repr >> (#field_offset);
                let actual_value: #field_ty = #field_decoded;
                let expected_value: #field_ty = #field_value;
                if actual_value != expected_value {
                    return None;
                }
            }));
            new_glue = field_ty.encode(field_value, &field_width);
        } else {
            // This is the more complicated case for non-constant fields.

            let field_decoded = field_ty.decode(quote!(field_as_repr), &field_width);
            let field_encoded = field_ty.encode(quote!(field), &field_width);
            new_glue = field_ty.encode(field_ident.to_token_stream(), &field_width);

            item_methods.push(Method {
                sig: quote!(#field_vis fn #field_getter_ident(&self) -> #field_ty),
                body: quote! {
                    let mut field_as_repr: ItemRepr = self.0 >> (#field_offset);

                    #field_decoded
                },
            });
            item_methods.push(Method {
                sig: quote!(#field_vis fn #field_setter_ident(&mut self, field: #field_ty)),
                body: quote! {
                    let mut field_as_repr: ItemRepr = #field_encoded;
                    self.0 &= !((!0 >> (ITEM_REPR_WIDTH - (#field_width))) << (#field_offset));
                    self.0 |= field_as_repr << (#field_offset);
                },
            });
            item_new_args.push(quote!(#field_ident: #field_ty));
        }
        new_stmts.push(quote! {
            bits <<= #field_width;
            bits |= #new_glue;
        });
    }

    let mut const_checks: Vec<syn::Expr> = Vec::new();
    if let Some(expected_width) = expected_width {
        match EnforceItemWidthStrategy::devise(expected_width, &item_width) {
            EnforceItemWidthStrategy::None => {},
            EnforceItemWidthStrategy::Fail(e) => {
                return e.into();
            }
            EnforceItemWidthStrategy::ConstCheck(check) => {
                const_checks.push(check);
            }
        }
    }
    // const _: () = { #(#const_checks ;)* }
    let const_checks: syn::Item = syn::ItemConst {
        attrs: Vec::new(),
        vis: syn::Visibility::Inherited,
        const_token: syn::Token![const](item_span),
        ident: syn::Ident::new("_", item_span),
        generics: Default::default(),
        colon_token: syn::Token![:](item_span),
        ty: Box::new(syn::TypeTuple {
            paren_token: syn::token::Paren(item_span),
            elems: Default::default(),
        } .into()),
        eq_token: syn::Token![=](item_span),
        expr: Box::new(syn::ExprBlock {
            attrs: Vec::new(),
            label: None,
            block: syn::Block {
                brace_token: syn::token::Brace(item_span),
                stmts: const_checks.into_iter().map(|expr| {
                    syn::Stmt::Expr(expr, Some(syn::Token![;](item_span)))
                })
                .collect(),
            },
        }
    .into()),
        semi_token: syn::Token![;](item_span),
    }
    .into();

    let item_repr =
        unwrap!(determine_item_repr(expected_width, item_span, &mut item_attrs, &item_width));

    item_new_stmts.reverse();
    item_methods.push(Method {
        sig: quote!(#item_vis fn new(#(#item_new_args),*) -> Self),
        body: quote! {
            let mut bits: ItemRepr = 0;
            #(#new_stmts)*

            Self(bits)
        },
    });

    let mut output = const_checks.into_token_stream();
    output.extend(Item {
        attrs: quote! {
            #(#item_attrs)*
            #[repr(transparent)]
        },
        vis: item_vis,
        token: quote!(struct),
        ident: item_ident,
        body: quote! { (#item_repr); },
        methods: item_methods,
        bitwise_impl: BitwiseImpl {
            width: item_width,
            repr: item_repr,
            from_repr_unchecked: quote!(Self(repr)),
            from_repr_checked: quote! {
                #from_repr_checked_body

                Some(Self(repr))
            },
            to_repr: quote!(self.0),
        },
    }
    .into_token_stream());

    output.into()
}

trait Endec {
    /// Generates an expression that produces a value of this type from a representation.
    fn decode(&self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr;

    /// Generates an expression that produces a representation from a value of this type.
    fn encode(&self, repr_width: Width, value_exprs: syn::Expr) -> syn::Expr;
}

impl Endec for Type {
    fn decode(&self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Prime(ty) => ty.decode(repr_width, repr_expr),
            _ => unsafe { self.decode_container(repr_width, repr_expr) },
        }
    }

    fn encode(&self, repr_width: Width, value_expr: syn::Expr) -> syn::Expr {
        match self {
            Self::Prime(ty) => ty.encode(repr_width, value_expr),
            _ => unsafe { self.encode_container(repr_width, value_expr) },
        }
    }
}

impl Type {
    unsafe fn decode_container(
        &self,
        repr_width: Width,
        repr_expr: syn::Expr,
    ) -> syn::Expr {
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

        // This closure generates a block that extracts the next element from a container
        // type (i.e., tuple or array).
        let get_elem_block = |elem_ty: &PrimeType| {
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
                    // let elem = #elem;
                    syn::Stmt::Local(syn::Local {
                        attrs: Vec::new(),
                        let_token,
                        pat: syn::PatIdent {
                            attrs: Vec::new(),
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
                    // #repr_expr >>= #elem_width;
                    syn::Stmt::Expr(
                        syn::ExprBinary {
                            attrs: Vec::new(),
                            left: Box::new(repr_expr),
                            op: syn::BinOp::ShrAssign(syn::Token![>>=](span)),
                            right: Box::new(elem_width.into_grouped_expr().into()),
                        }
                        .into(),
                        Some(semi_token),
                    ),
                    // elem
                    syn::Stmt::Expr(
                        syn::ExprPath {
                            attrs: Vec::new(),
                            qself: None,
                            path: elem_ident.into(),
                        }
                        .into(),
                        None,
                    ),
                ],
            }
        };
        type Elements = Punctuated<syn::Expr, syn::Token![,]>;
        // This closure produces a 2-tuple containing the local variable representing the
        // temporary container and an expression that evaluates to the final container, in
        // that order.
        let make_tmp_local_and_elems_expr =
            |elem_tys: &(dyn DoubleEndedIterator + ExactSizeIterator + Iterator<Item = PrimeType>),
             get_elem_expr: fn(&PrimeType) -> syn::Expr,
             make_accessor: fn(usize) -> syn::Expr,
             make_container: fn(Elements) -> syn::Expr| {
                let (tmp_elems, elems): (Elements, Elements) = (*elem_tys)
                    .enumerate()
                    .rev()
                    .map(|(i, elem_ty)| (get_elem_expr(elem_ty), make_accessor(i)))
                    .unzip();
                // let tmp = (#get_elem_block, #get_elem_block, ...);
                let tmp_local = syn::Local {
                    attrs: Vec::new(),
                    let_token,
                    pat: syn::PatIdent {
                        attrs: Vec::new(),
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
            Self::Prime(_) => std::hint::unreachable_unchecked(),
            Self::Tuple(elem_tys) => {
                let (tmp_local, elems_expr) = make_tmp_local_and_elems_expr(
                    elem_tys,
                    // #get_elem_block
                    |elem_ty| {
                        syn::ExprBlock {
                            attrs: Vec::new(),
                            label: None,
                            block: get_elem_block(elem_ty),
                        }
                        .into()
                    },
                    |i| {
                        // tmp.#i
                        syn::ExprField {
                            attrs: Vec::new(),
                            base: Box::new(
                                syn::ExprPath {
                                    attrs: Vec::new(),
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
                    |elems| syn::ExprTuple { attrs: Vec::new(), paren_token, elems }.into(),
                );

                syn::ExprBlock {
                    attrs: Vec::new(),
                    label: None,
                    block: syn::Block {
                        brace_token,
                        stmts: vec![
                            syn::Stmt::Local(tmp_local),
                            syn::Stmt::Expr(elems_expr, None),
                        ],
                    },
                }
                .into()
            }
            Self::Array { ty: elem_ty, len } => {
                // let get_elem = || #get_elem_block;
                let get_elem_local = syn::Local {
                    attrs: Vec::new(),
                    let_token,
                    pat: syn::PatIdent {
                        attrs: Vec::new(),
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
                                attrs: Vec::new(),
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
                                        attrs: Vec::new(),
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
                            attrs: Vec::new(),
                            func: Box::new(
                                syn::ExprPath {
                                    attrs: Vec::new(),
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
                            attrs: Vec::new(),
                            expr: Box::new(
                                syn::ExprPath {
                                    attrs: Vec::new(),
                                    qself: None,
                                    path: tmp_ident.into(),
                                }
                                .into(),
                            ),
                            bracket_token,
                            index: Box::new(syn::ExprLit {
                                attrs: Vec::new(),
                                // FIXME: span
                                lit: syn::LitInt::new(&i.to_string(), Span2::call_site()).into(),
                            }
                            .into()),
                        }
                        .into()
                    },
                    |elems| {
                        syn::ExprArray { attrs: Vec::new(), bracket_token, elems }.into()
                    },
                );

                // #get_elem_local
                // #tmp_local
                // #elems_expr
                syn::ExprBlock {
                    attrs: Vec::new(),
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

    unsafe fn encode_container(
        &self,
        repr_width: Width,
        value_expr: syn::Expr,
    ) -> syn::Expr {
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
        let repr_expr: syn::Expr =
            syn::ExprPath { attrs: Vec::new(), qself: None, path: repr_ident.into() }
                .into();
        // let repr = 0;
        let repr_local = syn::Local {
            attrs: Vec::new(),
            let_token,
            pat: syn::PatIdent {
                attrs: Vec::new(),
                by_ref: None,
                mutability: None,
                ident: repr_ident,
                subpat: None,
            }
            .into(),
            init: Some(syn::LocalInit {
                eq_token,
                expr: Box::new(
                    syn::ExprLit {
                        attrs: Vec::new(),
                        lit: syn::LitInt::new("0", span).into(),
                    }
                    .into(),
                ),
                diverge: None,
            }),
            semi_token,
        };
        // This closure generates a set of statements that collectively set the next element
        // in a container type (i.e., tuple or array).
        let set_elem_stmts = |elem_ty: &PrimeType, elem_expr| {
            let make_stmt = |op, right| {
                syn::Stmt::Expr(
                    syn::ExprBinary {
                        attrs: Vec::new(),
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
                    elem_ty.width().into_grouped_expr().into(),
                ),
                make_stmt(
                    syn::BinOp::BitOrAssign(syn::Token![|=](span)),
                    elem_ty.encode(repr_width, elem_expr),
                ),
            ]
        };

        match self {
            Self::Prime(_) => std::hint::unreachable_unchecked(),
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
                                    attrs: Vec::new(),
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
                    attrs: Vec::new(),
                    label: None,
                    block: syn::Block { brace_token, stmts },
                }
                .into()
            }
            Self::Array { ty: elem_ty, len } => {
                let i_ident = syn::Ident::new("i", span);
                // #value_expr[i]
                let elem_expr = syn::ExprIndex {
                    attrs: Vec::new(),
                    expr: Box::new(value_expr),
                    bracket_token,
                    index: Box::new(
                        syn::ExprPath {
                            attrs: Vec::new(),
                            qself: None,
                            path: i_ident.into(),
                        }
                        .into(),
                    ),
                }
                .into();
                // for i in ..#len {
                //     #set_elem_stmts
                // }
                let for_loop = syn::ExprForLoop {
                    attrs: Vec::new(),
                    label: None,
                    for_token,
                    pat: Box::new(
                        syn::PatIdent {
                            attrs: Vec::new(),
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
                            attrs: Vec::new(),
                            start: None,
                            limits: syn::RangeLimits::HalfOpen(dot_dot_token),
                            end: Some(Box::new(
                                syn::ExprLit {
                                    attrs: Vec::new(),
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
                    attrs: Vec::new(),
                    label: None,
                    block: syn::Block { brace_token, stmts },
                }
                .into()
            }
        }
    }
}

impl Endec for PrimeType {
    fn decode(&self, repr_width: Width, repr_expr: syn::Expr) -> syn::Expr {
        let span = repr_expr.span();
        let inner = syn::ExprBinary {
            attrs: Vec::new(),
            left: Box::new(repr_expr),
            op: syn::BinOp::BitAnd(syn::Token![&](span)),
            right: Box::new(repr_width.into_mask(repr_width).into()),
        }
        .into();

        match self {
            // #inner == 1
            Self::Bool => syn::ExprBinary {
                attrs: Vec::new(),
                left: Box::new(inner),
                op: syn::BinOp::Eq(syn::Token![==](span)),
                right: Box::new(
                    syn::ExprLit {
                        attrs: Vec::new(),
                        lit: syn::LitInt::new("1", span).into(),
                    }
                    .into(),
                ),
            }
            .into(),
            // #inner as _
            Self::UInt(_) => syn::ExprCast {
                attrs: Vec::new(),
                expr: Box::new(inner),
                as_token: syn::Token![as](span),
                ty: Box::new(
                    syn::TypeInfer { underscore_token: syn::Token![_](span) }.into(),
                ),
            }
            .into(),
            // unsafe { ::regent::Bitwise::from_repr_unchecked(#inner) }
            Self::Other(_) => syn::ExprUnsafe {
                attrs: Vec::new(),
                unsafe_token: syn::Token![unsafe](span),
                block: syn::Block {
                    brace_token: syn::token::Brace(span),
                    stmts: vec![syn::Stmt::Expr(
                        syn::ExprCall {
                            attrs: Vec::new(),
                            func: Box::new(
                                syn::ExprPath {
                                    attrs: Vec::new(),
                                    qself: None,
                                    path: syn::Path {
                                        leading_colon: Some(syn::Token![::](span)),
                                        segments: [
                                            "regent",
                                            "Bitwise",
                                            "from_repr_unchecked",
                                        ]
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
            attrs: Vec::new(),
            left: Box::new(match self {
                // ::regent::Bitwise::to_repr(#value_expr)
                Self::Other(_) => syn::ExprCall {
                    attrs: Vec::new(),
                    func: Box::new(
                        syn::ExprPath {
                            attrs: Vec::new(),
                            qself: None,
                            path: syn::Path {
                                leading_colon: Some(syn::Token![::](span)),
                                segments: ["regent", "Bitwise", "to_repr"]
                                    .into_iter()
                                    .collect(),
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
                    attrs: Vec::new(),
                    expr: Box::new(value_expr),
                    as_token: syn::Token![as](span),
                    ty: Box::new(
                        syn::ExprPath::from(syn::Ident::new("ItemRepr", span)).into(),
                    ),
                }
                .into(),
            }),
            op: syn::BinOp::BitAnd(syn::Token![&](span)),
            right: Box::new(repr_width.into_mask(repr_width).into()),
        }
        .into()
    }
}

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

#[derive(Clone)]
enum PrimeType {
    Bool,
    UInt(UIntType),
    Other(syn::TypePath),
}

impl PrimeType {
    fn parse(span: Span2, ty: syn::TypePath) -> Result<Self, TokenStream> {
        if let Some(ty) = ty.path.get_ident().map(ToString::to_string) {
            if ty == "bool" {
                return Ok(Self::Bool);
            } else if let Some(result) = UIntType::parse(span, &ty) {
                return result.map(Self::UInt);
            }
        }

        Ok(Self::Other(ty))
    }

    fn as_rust_primitive(self) -> Self {
        if let Self::UInt(ty) = self {
            Self::UInt(ty.round_up())
        } else {
            self
        }
    }

    fn exists(&self) -> bool {
        match self {
            Self::UInt(ty) => ty.exists(),
            _ => true,
        }
    }

    fn width(&self) -> Width {
        match self {
            Self::Bool => Width::Lit(1),
            Self::UInt(ty) => Width::Lit(ty.width),
            Self::Other(ty) => Width::Expr(quote!(<#ty as ::regent::Bitwise>::WIDTH)),
        }
    }
}

impl From<PrimeType> for syn::TypePath {
    fn from(ty: PrimeType) -> Self {
        match ty {
            Self::Bool => Self {
                qself: None,
                path: ["bool"].into_iter().collect(),
            },
            Self::UInt(ty) => ty.into(),
            Self::Other(ty) => ty,
        }
    }
}
