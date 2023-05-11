// SPDX-License-Identifier: MPL-2.0

//! The `bitwise` macro for structs.

// mod endec;

// use endec::Endec as _;
use super::*;

pub(crate) struct Struct;

impl Form for Struct {
    type Item = syn::ItemStruct;

    fn bitwise(_item: Self::Item) -> Result<Output<Self::Item>, Error> {
        todo!()

        /*
        check_generics(item.generics)?;
        let item_span = item.span();

        // These next few variables are default-initialized for now and will be continuously updated
        // during field processing.

        // This is the total bit-width of all fields.
        let mut item_width = Width::zero(item_span);
        let mut item_fn_blocks = vec![];
        // This is the list of all arguments accepted by `#item_ident::new`.
        let mut item_new_args = vec![];
        // This is a list of 'snippets' (or series of statements) that initialize the fields in
        // `#item_ident::new`.
        let mut item_new_stmts = vec![];
        // FIXME: name is inconsistent
        let mut from_repr_checked_body = TokenStream2::new();

        // Process fields.
        for (i, field) in item.fields.into_iter().enumerate() {
            let field_span = field.span();

            let field_ident = field.ident.unwrap_or_else(|| syn::Ident::new(&format!("f{i}"), field_span));

            let field_ty = Type::parse(field_span, field.ty)?;
            field_ty.validate(field_span)?;

            // This is the position of the least-significant bit of this field.
            let field_offset = item_width.clone();
            // This is the exact width of this field.
            let field_width = field_ty.width();
            item_width.add(&field_width);

            let field_ty = field_ty.as_rust_primitives();
            if !field_ty.exists() {
                return Err(err!(
                    field_span;
                    "'bitwise' field cannot be represented in terms of primitive Rust types"
                ));
            }

            let mut field_value = None;
            let field_args = FieldArgs::parse(field_span, &mut field.attrs)?;

            let new_glue: syn::Expr;
            if let Some(field_value) = field_args.constant {
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

        let item_repr =
            unwrap!(determine_item_repr(expected_width, item_span, &mut item_attrs, &item_width));

        item_methods.push(Method {
            sig: quote!(#item_vis fn new(#(#item_new_args),*) -> Self),
            body: quote! {
                let mut bits: ItemRepr = 0;
                #(#new_stmts)*

                Self(bits)
            },
        });

        let mut output = const_checks.into_token_stream();
        output.extend(
            Item {
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
            .into_token_stream(),
        );

        output.into()
        */
    }
}

/*
#[derive(Default)]
struct FieldArgs {
    constant: Option<syn::Expr>,
}

impl FieldArgs {
    fn parse(span: Span2, attrs: &mut Vec<syn::Attribute>) -> Result<Self, Error> {
        let mut result = Self::default();

        let as_token = syn::Token![as](span);
        let gt_token = syn::Token![>](span);
        let lt_token = syn::Token![<](span);
        let paren_token = syn::token::Paren(span);
        let path_sep_token = syn::Token![::](span);
        let underscore_token = syn::Token![_](span);

        attrs.retain(|attr| match attr.meta {
            syn::Meta::Path(path) if path.is_ident("constant") => {
                let fn_qself = syn::QSelf {
                    lt_token,
                    ty: Box::new(syn::TypeInfer { underscore_token }.into()),
                    position: 3,
                    as_token: Some(as_token),
                    gt_token,
                };
                let fn_path = syn::Path {
                    leading_colon: Some(path_sep_token),
                    segments: ["core", "default", "Default", "default"].into_iter().collect(),
                };

                result.constant = Some(
                    syn::ExprCall {
                        attrs: vec![],
                        func: Box::new(
                            syn::ExprPath { attrs: vec![], qself: Some(fn_qself), path: fn_path }
                                .into(),
                        ),
                        paren_token,
                        args: Default::default(),
                    }
                    .into(),
                );

                true
            }
            syn::Meta::NameValue(pair) if pair.path.is_ident("constant") => {
                result.constant = Some(pair.value);

                true
            }
            _ => false,
        });

        Ok(result)
    }
}

/// Creates a [`syn::Expr`] that masks the least-significant bits of an expression.
///
/// The expression is of the form:
///
/// ```no_run
/// (!0 >> (#repr_width - #width))
/// ```
fn make_mask(repr_width: Width, width: Width) -> syn::Expr {
    let span = self.span();

    let zero_lit = syn::ExprLit { attrs: vec![], lit: syn::LitInt::new("0", span).into() }.into();
    let lhs_expr = syn::ExprUnary {
        attrs: vec![],
        op: syn::UnOp::Not(syn::Token![!](span)),
        expr: Box::new(zero_lit),
    }
    .into();

    let rhs_expr = syn::ExprBinary {
        attrs: vec![],
        left: Box::new(repr_width.into_expr()),
        op: syn::BinOp::Sub(syn::Token![-](span)),
        right: Box::new(self.into_expr()),
    }
    .into();

    syn::ExprParen {
        attrs: vec![],
        paren_token: syn::token::Paren(span),
        expr: Box::new(
            syn::ExprBinary {
                attrs: vec![],
                left: Box::new(lhs_expr),
                op: syn::BinOp::Shr(syn::Token![>>](span)),
                right: Box::new(rhs_expr),
            }
            .into(),
        ),
    }
    .into()
}
*/
