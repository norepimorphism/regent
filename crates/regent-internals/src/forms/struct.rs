// SPDX-License-Identifier: MPL-2.0

//! The `bitwise` macro for structs.

mod field;

use field::Field;

use super::*;

pub(crate) struct Struct;

impl Form for Struct {
    type Item = syn::ItemStruct;

    fn bitwise(mut item: Self::Item) -> Result<Output<Self::Item>> {
        check_generics(&item.generics)?;

        let item_span = item.span();
        // This is the total bit-width of all fields.
        let mut item_width = Width::Met(item_span, 0);

        // Pre-process the fields to compute `item_width`.
        let fields: Vec<Field> = item
            .fields
            .into_iter()
            .enumerate()
            .map(|(i, field)| {
                let field = Field::parse(i, field)?;
                item_width = Width::add(item_width.clone(), field.width.clone());

                Ok(field)
            })
            .collect::<Result<_>>()?;

        // This is the representation, or storage type, of the struct.
        let item_repr =
            uint::RustType::repr_for_item(item_span, &item_width, &mut item.attrs, |attrs, i| {
                // Remove the `#[repr]` attribute, if any, because we will replace it.
                attrs.remove(i);
            })?;
        // Add a `#[repr(transparent)]` outer attribute.
        item.attrs.push(syn::Attribute {
            pound_token: syn::Token![#](item_span),
            style: syn::AttrStyle::Outer,
            bracket_token: syn::token::Bracket(item_span),
            meta: syn::MetaList {
                path: path!(item_span; repr),
                delimiter: syn::MacroDelimiter::Paren(syn::token::Paren(item_span)),
                tokens: syn::Ident::new("transparent", item_span).into_token_stream(),
            }
            .into(),
        });

        // These are the associated functions within the `Output::impl_item` impl block.
        let mut impl_item_fns: Vec<syn::ImplItemFn> = vec![];
        // This is the body of `Bitwise::from_repr_checked`.
        let mut from_repr_checked_body: Vec<syn::Stmt> = vec![];
        let mut new_fn_args: Vec<syn::PatType> = vec![];
        let mut new_fn_body: Vec<syn::Stmt> = vec![];

        // Process the fields again to fill `impl_item_fns` and `from_repr_checked_body`

        // This is the bit offset of the field currently being processed.
        //
        // 0 means least-significant.
        let mut field_offset = Width::Met(item_span, 0);
        for field in fields.into_iter().rev() {
            let span = field.span;

            let brace_token = syn::token::Brace(span);
            let eq_token = syn::Token![=](span);
            let if_token = syn::Token![if](span);
            let let_token = syn::Token![let](span);
            let ne_token = syn::Token![!=](span);
            let return_token = syn::Token![return](span);
            let semi_token = syn::Token![;](span);
            let shr_token = syn::Token![>>](span);

            // This is the `syn::Ident` of the getter method.
            let getter_ident = field.ident.clone();
            // This closure produces a getter method as a `syn::ImplItem`.
            let make_getter = |is_const: bool, stmts| {
                syn::ImplItemFn {
                    attrs: field.attrs,
                    vis: field.vis.clone(),
                    defaultness: None,
                    sig: if is_const {
                        sig::Builder::new().with_const()
                    } else {
                        sig::Builder::new().with_receiver(Receiver::new_ref_self())
                    }
                    .build(
                        span,
                        getter_ident.clone(),
                        |_| [],
                        |_| Some(field.api_ty.clone()),
                    ),
                    block: syn::Block { brace_token, stmts },
                }
                .into()
            };
            let repr_width = item_repr.width();

            let new_glue: syn::Expr;
            if let Some(constant) = field.constant {
                // Add the getter method.
                impl_item_fns
                    .push(make_getter(true, vec![syn::Stmt::Expr(constant.clone(), None)]));
                new_glue = constant.clone();
                // Add to `from_repr_checked_body`.
                from_repr_checked_body.extend([
                    // let repr = repr >> #field_offset;
                    syn::Stmt::Local(syn::Local {
                        attrs: vec![],
                        let_token,
                        pat: pat_path!(span; repr),
                        init: Some(syn::LocalInit {
                            eq_token,
                            expr: Box::new(
                                syn::ExprBinary {
                                    attrs: vec![],
                                    left: Box::new(expr_path!(span; repr)),
                                    op: syn::BinOp::Shr(shr_token),
                                    right: Box::new(field_offset.clone().parenthesize().into()),
                                }
                                .into(),
                            ),
                            diverge: None,
                        }),
                        semi_token,
                    }),
                    // if /* extract */ != #constant {
                    //     return None;
                    // }
                    syn::Stmt::Expr(
                        syn::ExprIf {
                            attrs: vec![],
                            if_token,
                            cond: Box::new(
                                syn::ExprBinary {
                                    attrs: vec![],
                                    left: Box::new(parenthesize((field.extract)(
                                        repr_width,
                                        expr_path!(span; repr),
                                    ))),
                                    op: syn::BinOp::Ne(ne_token),
                                    right: Box::new(constant),
                                }
                                .into(),
                            ),
                            then_branch: blockify(syn::ExprReturn {
                                attrs: vec![],
                                return_token,
                                expr: Some(Box::new(
                                    expr_path!(span; ::core::option::Option::None),
                                )),
                            }),
                            else_branch: None,
                        }
                        .into(),
                        None,
                    ),
                ]);
            } else {
                // This is the `syn::Ident` of the setter method.
                let setter_ident =
                    syn::Ident::new(&format!("set_{getter_ident}"), getter_ident.span());

                new_glue = (field.extract)(repr_width, expr_path!(span; repr));
                // Add to `impl_item_fns`.
                impl_item_fns.extend([
                    make_getter(
                        false,
                        vec![syn::Stmt::Expr(
                            (field.extract)(
                                repr_width,
                                syn::ExprBinary {
                                    attrs: vec![],
                                    left: Box::new(
                                        syn::ExprField {
                                            attrs: vec![],
                                            base: Box::new(expr_path!(span; self)),
                                            dot_token: syn::Token![.](span),
                                            member: syn::Member::Unnamed(0.into()),
                                        }
                                        .into(),
                                    ),
                                    op: syn::BinOp::Shr(syn::Token![>>](span)),
                                    right: Box::new(field_offset.clone().parenthesize().into()),
                                }
                                .into(),
                            ),
                            None,
                        )],
                    ),
                    syn::ImplItemFn {
                        attrs: vec![],
                        vis: field.vis,
                        defaultness: None,
                        sig: sig::Builder::new().with_receiver(Receiver::new_ref_mut_self()).build(
                            span,
                            setter_ident,
                            |span| {
                                [syn::PatType {
                                    attrs: vec![],
                                    pat: Box::new(
                                        syn::PatIdent {
                                            attrs: vec![],
                                            by_ref: None,
                                            mutability: None,
                                            ident: syn::Ident::new("field", span),
                                            subpat: None,
                                        }
                                        .into(),
                                    ),
                                    colon_token: syn::Token![:](span),
                                    ty: Box::new(field.api_ty.clone()),
                                }]
                            },
                            |_| None,
                        ),
                        block: syn::Block {
                            brace_token: syn::token::Brace(span),
                            // let mut field_as_repr: ItemRepr = #field_encoded;
                            // self.0 &= !((!0 >> (ITEM_REPR_WIDTH - (#field_width))) <<
                            // (#field_offset)); self.0 |= field_as_repr
                            // << (#field_offset);
                            stmts: vec![],
                        },
                    },
                ]);
                // Add to `new_fn_args`.
                new_fn_args.push(syn::PatType {
                    attrs: vec![],
                    pat: Box::new(
                        syn::PatIdent {
                            attrs: vec![],
                            by_ref: None,
                            mutability: None,
                            ident: field.ident,
                            subpat: None,
                        }
                        .into(),
                    ),
                    colon_token: syn::Token![:](span),
                    ty: Box::new(field.api_ty),
                });
            }
            // Add to `new_fn_body`.
            new_fn_body.extend([
                syn::Stmt::Expr(
                    syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(expr_path!(span; repr)),
                        op: syn::BinOp::ShlAssign(syn::Token![<<=](span)),
                        right: Box::new(field.width.clone().into()),
                    }
                    .into(),
                    Some(syn::Token![;](span)),
                ),
                syn::Stmt::Expr(
                    syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(expr_path!(span; repr)),
                        op: syn::BinOp::BitOrAssign(syn::Token![|=](span)),
                        right: Box::new(new_glue),
                    }
                    .into(),
                    Some(syn::Token![;](span)),
                ),
            ]);
            // Update `field_offset`.
            field_offset = Width::add(field_offset, field.width);
        }

        let brace_token = syn::token::Brace(item_span);
        let dot_token = syn::Token![.](item_span);
        let eq_token = syn::Token![=](item_span);
        let impl_token = syn::Token![impl](item_span);
        let let_token = syn::Token![let](item_span);
        let paren_token = syn::token::Paren(item_span);
        let semi_token = syn::Token![;](item_span);

        item.fields = syn::Fields::Unnamed(syn::FieldsUnnamed {
            paren_token,
            unnamed: once(syn::Field {
                attrs: vec![],
                vis: syn::Visibility::Inherited,
                mutability: syn::FieldMutability::None,
                ident: None,
                colon_token: None,
                ty: item_repr.into_syn_type(item_span),
            })
            .collect(),
        });

        // Add the `new` function.
        impl_item_fns.push(syn::ImplItemFn {
            attrs: vec![],
            vis: item.vis.clone(),
            defaultness: None,
            sig: sig::Builder::new().build(
                item_span,
                syn::Ident::new("new", item_span),
                |_| new_fn_args,
                |span| Some(ty_path!(span; Self)),
            ),
            block: syn::Block {
                brace_token,
                stmts: once(syn::Stmt::Local(syn::Local {
                    attrs: vec![],
                    let_token,
                    pat: pat_path!(item_span; repr),
                    init: Some(syn::LocalInit {
                        eq_token,
                        expr: Box::new(
                            syn::ExprLit {
                                attrs: vec![],
                                lit: syn::LitInt::new("0", item_span).into(),
                            }
                            .into(),
                        ),
                        diverge: None,
                    }),
                    semi_token,
                }))
                .chain(new_fn_body)
                .chain(once(syn::Stmt::Expr(
                    syn::ExprCall {
                        attrs: vec![],
                        func: Box::new(expr_path!(item_span; Self)),
                        paren_token,
                        args: once::<syn::Expr>(expr_path!(item_span; repr)).collect(),
                    }
                    .into(),
                    None,
                )))
                .collect(),
            },
        });

        // We are now ready to build the `Output` type.

        let impl_item = syn::ItemImpl {
            attrs: vec![],
            defaultness: None,
            unsafety: None,
            impl_token,
            generics: Default::default(),
            trait_: None,
            self_ty: Box::new(ty_path!(item.ident.clone())),
            brace_token,
            items: impl_item_fns.into_iter().map(syn::ImplItem::from).collect(),
        };

        // This is the `from_repr_unchecked` method.
        //
        // This looks like:
        //   Self(repr)
        let from_repr_unchecked = syn::ExprCall {
            attrs: vec![],
            func: Box::new(expr_path!(item_span; Self)),
            paren_token,
            args: once::<syn::Expr>(expr_path!(item_span; repr)).collect(),
        };
        // This is the `from_repr_checked` method.
        //
        // This looks like:
        //   #from_repr_checked_body
        //   Some(#from_repr_unchecked)
        let from_repr_checked = syn::Block {
            brace_token,
            stmts: from_repr_checked_body
                .into_iter()
                .chain(once(syn::Stmt::Expr(
                    syn::ExprCall {
                        attrs: vec![],
                        func: Box::new(expr_path!(item_span; ::core::option::Option::Some)),
                        paren_token,
                        args: once(syn::Expr::from(from_repr_unchecked.clone())).collect(),
                    }
                    .into(),
                    None,
                )))
                .collect(),
        };
        let from_repr_unchecked = blockify(from_repr_unchecked);
        // This is the `to_repr` method.
        //
        // This looks like:
        //   self.0
        let to_repr = blockify(syn::ExprField {
            attrs: vec![],
            base: Box::new(expr_path!(item_span; self)),
            dot_token,
            member: syn::Member::Unnamed(0.into()),
        });
        // This is the `into_repr` method.
        let into_repr = to_repr.clone();

        let impl_bitwise_for_item = BitwiseImpl {
            ident: item.ident.clone(),
            width: item_width,
            repr: item_repr,
            funcs: BitwiseFuncs { from_repr_unchecked, from_repr_checked, to_repr, into_repr },
        };

        Ok(Output { item, impl_item: Some(impl_item), impl_bitwise_for_item })
    }
}
