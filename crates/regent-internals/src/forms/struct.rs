// SPDX-License-Identifier: MPL-2.0

//! The `bitwise` macro for structs.

mod field;

use field::{Field, Represented as _};

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
                // FIXME: it sucks that we clone `item_width` here, but alas
                // `std::mem::replace_with` doesn't exist
                item_width = Width::add(item_width.clone(), field.pseudo_ty.width());

                Ok(field)
            })
            .collect::<Result<_>>()?;

        let mut const_ctx = vec![];
        // This is the representation, or storage type, of the struct.
        let item_repr = uint::RustType::repr_for_item(
            item_span,
            &item.ident,
            &item_width,
            &mut item.attrs,
            &mut const_ctx,
            |attrs, i| {
                // Remove the `#[repr]` attribute, if present, because we will replace it.
                attrs.remove(i);
            },
        )?;
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

        // Process the fields again to fill `impl_item_fns` and `from_repr_checked_body`.

        // This is the bit offset of the field currently being processed.
        //
        // 0 means least-significant.
        let mut field_offset = Width::Met(item_span, 0);
        for field in fields.into_iter() {
            let span = field.span;

            let dot_token = syn::Token![.](span);
            let eq_token = syn::Token![=](span);
            let if_token = syn::Token![if](span);
            let let_token = syn::Token![let](span);
            let ne_token = syn::Token![!=](span);
            let or_eq_token = syn::Token![|=](span);
            let return_token = syn::Token![return](span);
            let semi_token = syn::Token![;](span);
            let shl_eq_token = syn::Token![<<=](span);
            let shr_token = syn::Token![>>](span);

            let api_ty = {
                let span = field.pseudo_ty.span();

                field
                    .pseudo_ty
                    .clone()
                    .try_into_api_type()
                    .ok_or_else(|| err!(span; "this cannot be made into an API type"))?
            };

            let repr_width = item_repr.width();

            let new_glue: syn::Expr;
            if let Some(constant) = field.constant {
                // Add the getter function.
                impl_item_fns.push(make_getter_fn(
                    span,
                    field.attrs,
                    field.vis,
                    true,
                    field.ident.clone(),
                    api_ty,
                    vec![syn::Stmt::Expr(constant.clone(), None)],
                ));
                new_glue = constant.clone();
                // Add to `from_repr_checked_body`.
                if !matches!(field_offset, Width::Met(_, 0)) {
                    // Rendered:
                    //   let repr = repr >> (#field_offset);
                    from_repr_checked_body.push(syn::Stmt::Local(syn::Local {
                        attrs: vec![],
                        let_token,
                        pat: syn::PatIdent {
                            attrs: vec![],
                            by_ref: None,
                            mutability: None,
                            ident: syn::Ident::new("repr", span),
                            subpat: None,
                        }
                        .into(),
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
                    }));
                }
                // Rendered:
                //   if (/* field.pseudo_ty.extract() */) != #constant {
                //       return None;
                //   }
                from_repr_checked_body.push(syn::Stmt::Expr(
                    syn::ExprIf {
                        attrs: vec![],
                        if_token,
                        cond: Box::new(
                            syn::ExprBinary {
                                attrs: vec![],
                                left: Box::new(parenthesize(
                                    field.pseudo_ty.extract(repr_width, expr_path!(span; repr)),
                                )),
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
                ));
            } else {
                new_glue = field.pseudo_ty.extract(repr_width, expr_path!(span; repr));
                // Add the getter method.
                impl_item_fns.push(make_getter_fn(
                    span,
                    field.attrs,
                    field.vis.clone(),
                    false,
                    field.ident.clone(),
                    api_ty.clone(),
                    vec![syn::Stmt::Expr(
                        field.pseudo_ty.extract(
                            repr_width,
                            syn::ExprBinary {
                                attrs: vec![],
                                left: Box::new(
                                    syn::ExprField {
                                        attrs: vec![],
                                        base: Box::new(expr_path!(span; self)),
                                        dot_token,
                                        member: syn::Member::Unnamed(syn::Index { index: 0, span }),
                                    }
                                    .into(),
                                ),
                                op: syn::BinOp::Shr(shr_token),
                                right: Box::new(field_offset.clone().parenthesize().into()),
                            }
                            .into(),
                        ),
                        None,
                    )],
                ));
                // Add the setter method.
                impl_item_fns.push(make_setter_fn(
                    span,
                    field.vis.clone(),
                    &field.ident,
                    api_ty.clone(),
                    repr_width,
                    field.pseudo_ty.width(),
                    field_offset.clone(),
                ));
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
                    ty: Box::new(api_ty),
                });
            }
            // Add to `new_fn_body`.
            if !matches!(field_offset, Width::Met(_, 0)) {
                // Rendered:
                //   repr <<= /* field.pseudo_ty.width() */;
                new_fn_body.push(syn::Stmt::Expr(
                    syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(expr_path!(span; repr)),
                        op: syn::BinOp::ShlAssign(shl_eq_token),
                        right: Box::new(field.pseudo_ty.width().into()),
                    }
                    .into(),
                    Some(semi_token),
                ));
            }
            // Rendered:
            //   repr |= #new_glue;
            new_fn_body.push(syn::Stmt::Expr(
                syn::ExprBinary {
                    attrs: vec![],
                    left: Box::new(expr_path!(span; repr)),
                    op: syn::BinOp::BitOrAssign(or_eq_token),
                    right: Box::new(new_glue),
                }
                .into(),
                Some(semi_token),
            ));
            // Update `field_offset`.
            field_offset = Width::add(field_offset, field.pseudo_ty.width());
        }

        let brace_token = syn::token::Brace(item_span);
        let dot_token = syn::Token![.](item_span);
        let impl_token = syn::Token![impl](item_span);
        let paren_token = syn::token::Paren(item_span);

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
        impl_item_fns.push(make_new_fn(item_span, item.vis.clone(), new_fn_args, new_fn_body));

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
        // Rendered:
        //   Self(repr)
        let from_repr_unchecked = syn::ExprCall {
            attrs: vec![],
            func: Box::new(expr_path!(item_span; Self)),
            paren_token,
            args: once::<syn::Expr>(expr_path!(item_span; repr)).collect(),
        };
        // This is the `from_repr_checked` method.
        //
        // Rendered:
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
        // Rendered:
        //   self.0
        let to_repr = blockify(syn::ExprField {
            attrs: vec![],
            base: Box::new(expr_path!(item_span; self)),
            dot_token,
            member: syn::Member::Unnamed(syn::Index { index: 0, span: item_span }),
        });
        // This is the `into_repr` method.
        let into_repr = to_repr.clone();

        let impl_bitwise_for_item = BitwiseImpl {
            ident: item.ident.clone(),
            width: item_width,
            repr: item_repr,
            funcs: BitwiseFuncs { from_repr_unchecked, from_repr_checked, to_repr, into_repr },
        };

        Ok(Output { const_ctx, item, impl_item: Some(impl_item), impl_bitwise_for_item })
    }
}

fn make_getter_fn(
    span: Span2,
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    is_const: bool,
    ident: syn::Ident,
    output: syn::Type,
    stmts: Vec<syn::Stmt>,
) -> syn::ImplItemFn {
    let sig = if is_const {
        sig::Builder::new().with_const()
    } else {
        sig::Builder::new().with_receiver(Receiver::new_ref_self())
    }
    .build(span, ident, |_| [], |_| Some(output));

    syn::ImplItemFn {
        attrs,
        vis,
        defaultness: None,
        sig,
        block: syn::Block { brace_token: syn::token::Brace(span), stmts },
    }
}

fn make_setter_fn(
    span: Span2,
    vis: syn::Visibility,
    ident: &syn::Ident,
    input: syn::Type,
    repr_width: usize,
    field_width: Width,
    field_offset: Width,
) -> syn::ImplItemFn {
    // Common identifiers.
    let field_ident = syn::Ident::new("field", span);
    // Common tokens.
    let and_token = syn::Token![&](span);
    let and_eq_token = syn::Token![&=](span);
    let or_eq_token = syn::Token![|=](span);
    let dot_token = syn::Token![.](span);
    let not_token = syn::Token![!](span);
    let semi_token = syn::Token![;](span);
    let shl_token = syn::Token![<<](span);

    let sig = sig::Builder::new().with_receiver(Receiver::new_ref_mut_self()).build(
        span,
        syn::Ident::new(&format!("set_{}", ident), ident.span()),
        |span| {
            [syn::PatType {
                attrs: vec![],
                pat: Box::new(
                    syn::PatIdent {
                        attrs: vec![],
                        by_ref: None,
                        mutability: None,
                        ident: field_ident.clone(),
                        subpat: None,
                    }
                    .into(),
                ),
                colon_token: syn::Token![:](span),
                ty: Box::new(input),
            }]
        },
        |_| None,
    );

    // Rendered:
    //   self.0
    let self_0_expr: syn::Expr = syn::ExprField {
        attrs: vec![],
        base: Box::new(expr_path!(span; self)),
        dot_token,
        member: syn::Member::Unnamed(syn::Index { index: 0, span }),
    }
    .into();
    let mask_expr = mask(Width::Met(span, repr_width), field_width);

    let mut stmts = vec![];
    // Rendered:
    //   self.0 &= !(#mask_expr << (#field_offset));
    stmts.push(syn::Stmt::Expr(
        syn::ExprBinary {
            attrs: vec![],
            left: Box::new(self_0_expr.clone()),
            op: syn::BinOp::BitAndAssign(and_eq_token),
            right: Box::new(
                syn::ExprUnary {
                    attrs: vec![],
                    op: syn::UnOp::Not(not_token),
                    expr: Box::new(parenthesize(syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(mask_expr.clone()),
                        op: syn::BinOp::Shl(shl_token),
                        right: Box::new(field_offset.parenthesize().into()),
                    })),
                }
                .into(),
            ),
        }
        .into(),
        Some(semi_token),
    ));
    // Rendered:
    //   self.0 |= field & #mask_expr;
    stmts.push(syn::Stmt::Expr(
        syn::ExprBinary {
            attrs: vec![],
            left: Box::new(self_0_expr),
            op: syn::BinOp::BitOrAssign(or_eq_token),
            right: Box::new(
                syn::ExprBinary {
                    attrs: vec![],
                    left: Box::new(expr_path!(field_ident)),
                    op: syn::BinOp::BitAnd(and_token),
                    right: Box::new(mask_expr),
                }
                .into(),
            ),
        }
        .into(),
        Some(semi_token),
    ));

    syn::ImplItemFn {
        attrs: vec![],
        vis,
        defaultness: None,
        sig,
        block: syn::Block { brace_token: syn::token::Brace(span), stmts },
    }
}

fn make_new_fn(
    span: Span2,
    vis: syn::Visibility,
    args: Vec<syn::PatType>,
    body: Vec<syn::Stmt>,
) -> syn::ImplItemFn {
    let repr_ident = syn::Ident::new("repr", span);

    // Rendered:
    //   fn new(#args) -> Self
    let sig = sig::Builder::new().build(
        span,
        syn::Ident::new("new", span),
        |_| args,
        |span| Some(ty_path!(span; Self)),
    );
    // Rendered:
    //   let mut repr = 0;
    //   #body
    //   Self(repr)
    let stmts = once(syn::Stmt::Local(syn::Local {
        attrs: vec![],
        let_token: syn::Token![let](span),
        pat: syn::PatIdent {
            attrs: vec![],
            by_ref: None,
            mutability: Some(syn::Token![mut](span)),
            ident: repr_ident.clone(),
            subpat: None,
        }
        .into(),
        init: Some(syn::LocalInit {
            eq_token: syn::Token![=](span),
            expr: Box::new(
                syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("0", span).into() }.into(),
            ),
            diverge: None,
        }),
        semi_token: syn::Token![;](span),
    }))
    .chain(body)
    .chain(once(syn::Stmt::Expr(
        syn::ExprCall {
            attrs: vec![],
            func: Box::new(expr_path!(span; Self)),
            paren_token: syn::token::Paren(span),
            args: once::<syn::Expr>(expr_path!(repr_ident)).collect(),
        }
        .into(),
        None,
    )))
    .collect();

    syn::ImplItemFn {
        attrs: vec![],
        vis,
        defaultness: None,
        sig,
        block: syn::Block { brace_token: syn::token::Brace(span), stmts },
    }
}
