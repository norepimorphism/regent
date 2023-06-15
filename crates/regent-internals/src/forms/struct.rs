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
            .rev()
            .map(|(i, field)| Field::parse(i, &mut item_width, field))
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
        //
        // We reserve one slot for `new` and another two slots for each field to accommodate getters
        // and setters.
        let mut impl_item_fns: Vec<syn::ImplItemFn> = Vec::with_capacity(1 + (2 * fields.len()));
        // This is the `new` function.
        let mut new_fn =
            NewFn { span: item_span, vis: item.vis.clone(), args: vec![], body: vec![] };

        // Process the fields again in most-significant to least-significant order to fill
        // `impl_item_fns` and `new_fn`.
        for field in fields.iter() {
            let span = field.span;

            let colon_token = syn::Token![:](span);
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

            let repr_width = item_repr.width();
            new_fn.update_with_field(repr_width, field);
            /*
            if let Some(constant) = field.constant.clone() {
                // Add the getter function.
                impl_item_fns.push(make_getter_fn(
                    span,
                    field.attrs.clone(),
                    field.vis.clone(),
                    true,
                    field.ident.clone(),
                    api_ty,
                    vec![syn::Stmt::Expr(constant.clone(), None)],
                ));
                // Add to `from_repr_checked_body`.
                /*
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
                */
            } else {
                // Add the getter method.
                impl_item_fns.push(make_getter_fn(
                    span,
                    field.attrs.clone(),
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
                    field.api_ty.clone(),
                    repr_width,
                    field.pseudo_ty.width(),
                    field.offset.clone(),
                ));
            }*/
        }

        // This is the body of `Bitwise::from_repr_checked`.
        let mut from_repr_checked_body: Vec<syn::Stmt> = vec![];

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
        impl_item_fns.push(new_fn.into());

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

struct Ctors {
    span: Span2,
    vis: syn::Visibility,
    args: Vec<syn::PatType>,
    body: Vec<syn::Stmt>,
}

impl NewFn {
    fn update_with_field(&mut self, repr_width: usize, field: &Field) {
        let span = field.span;

        // Common expressions.
        let repr_expr: syn::Expr = expr_path!(span; repr);
        // Common tokens.
        let colon_token = syn::Token![:](span);
        let or_eq_token = syn::Token![|=](span);
        let semi_token = syn::Token![;](span);
        let shl_eq_token = syn::Token![<<=](span);

        if field.constant.is_none() {
            // Rendered:
            //   /* field.ident */: /* field.api_ty */
            self.args.push(syn::PatType {
                attrs: vec![],
                pat: Box::new(
                    syn::PatIdent {
                        attrs: vec![],
                        by_ref: None,
                        mutability: None,
                        ident: field.ident.clone(),
                        subpat: None,
                    }
                    .into(),
                ),
                colon_token,
                ty: Box::new(field.api_ty.clone()),
            });
        }

        // If this is not the first field, we need to left-shift the previous field out of the way.
        if field.index > 0 {
            // Rendered:
            //   repr <<= /* field.pseudo_ty.width() */;
            self.body.push(syn::Stmt::Expr(
                syn::ExprBinary {
                    attrs: vec![],
                    left: Box::new(repr_expr.clone()),
                    op: syn::BinOp::ShlAssign(shl_eq_token),
                    right: Box::new(field.pseudo_ty.width().into()),
                }
                .into(),
                Some(semi_token),
            ));
        }

        let field_value = match &field.constant {
            Some(it) => it.clone(),
            None => field.pseudo_ty.extract(repr_width, repr_expr.clone()),
        };
        // Rendered:
        //   repr |= #field_value;
        self.body.push(syn::Stmt::Expr(
            syn::ExprBinary {
                attrs: vec![],
                left: Box::new(repr_expr),
                op: syn::BinOp::BitOrAssign(or_eq_token),
                right: Box::new(field_value),
            }
            .into(),
            Some(semi_token),
        ));
    }
}

impl From<NewFn> for syn::ImplItemFn {
    fn from(new_fn: NewFn) -> Self {
        let span = new_fn.span;
        let repr_ident = syn::Ident::new("repr", span);

        // Rendered:
        //   fn new(/* new_fn.args */) -> Self
        let sig = sig::Builder::new().build(
            span,
            syn::Ident::new("new", span),
            |_| new_fn.args,
            |span| Some(ty_path!(span; Self)),
        );
        // Rendered:
        //   let mut repr = 0;
        //   /* new_fn.body */
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
        .chain(new_fn.body)
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
            vis: new_fn.vis,
            defaultness: None,
            sig,
            block: syn::Block { brace_token: syn::token::Brace(span), stmts },
        }
    }
}
