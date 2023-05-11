// SPDX-License-Identifier: MPL-2.0

//! The `bitwise` macro for structs.

mod repr;
mod field;

use repr::HasRepr as _;
use super::*;

pub(crate) struct Struct;

impl Form for Struct {
    type Item = syn::ItemStruct;

    fn bitwise(item: Self::Item) -> Result<Output<Self::Item>, Error> {
        check_generics(&item.generics)?;

        let item_span = item.span();

        // Common tokens with span `item_span`.
        let brace_token = syn::token::Brace(item_span);
        let impl_token = syn::Token![impl](item_span);
        let paren_token = syn::token::Paren(item_span);

        // This corresponds to `Output::impl_item`. We will fill the `items` field as we go.
        let mut impl_item = syn::ItemImpl {
            attrs: vec![],
            defaultness: None,
            unsafety: None,
            impl_token,
            generics: Default::default(),
            trait_: None,
            self_ty: Box::new(type_path!(item.ident.clone())),
            brace_token,
            items: vec![],
        };

        // This is the total bit-width of all fields.
        let mut item_width = Width::zero(item_span);

        // Note: we can use `into_iter` here because we will later replace `item.fields` with a
        // single field for the item representation.
        for (i, field) in item.fields.into_iter().enumerate() {
            // This is the field type 'as written'.
            let ty = field::Type::parse(field.ty)?;
            // This is the bit-width of the field according to `ty`.
            let width = ty.width();
            // Update the total item width before we forget.
            item_width = Width::add(item_width, width);
            // This is the API-friendly version of the field type (e.g., `u8` instead of `u5`).
            let ty = ty.try_into_api_type()?;

            let args = field::Args::parse(&mut field.attrs)?;

            let span = field.span();
            // This is the `syn::Ident` of the getter method.
            let getter_ident = field.ident.unwrap_or_else(|| syn::Ident::new(&format!("f{i}"), span));
            // This closure produces a getter method as a `syn::ImplItem`.
            let make_getter = |is_const: bool, stmts| syn::ImplItemFn {
                attrs: field.attrs,
                vis: field.vis,
                defaultness: None,
                sig: syn::Signature {
                    constness: is_const.then_some(syn::Token![const](span)),
                    asyncness: None,
                    unsafety: None,
                    abi: None,
                    fn_token: syn::Token![fn](span),
                    ident: getter_ident,
                    generics: Default::default(),
                    paren_token: syn::token::Paren(span),
                    inputs: Punctuated::new(),
                    variadic: None,
                    output: syn::ReturnType::Type(syn::Token![->](span), Box::new(ty.into())),
                },
                block: syn::Block { brace_token: syn::token::Brace(span), stmts },
            }
            .into();

            let new_glue: syn::Expr;
            if let Some(constant_value) = args.constant {
                // This is the simple case for a constant field. We only need to generate a getter
                // method.

                let decoded = ty.decode(quote!(repr), &field_width);
                // This is the getter method.
                let getter = make_getter(true, vec![]);
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
                // This is the complex case for a non-constant field. We need to generate both
                // getter and setter methods.

                // This is the `syn::Ident` of the setter method.
                let setter_ident = syn::Ident::new(&format!("set_{getter_ident}"), getter_ident.span());

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
            uint::RustType::repr_for_item(item_span, &item_width, &mut item.attrs)?;

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
