// SPDX-License-Identifier: MPL-2.0

//! The `bitwise` macro for enums.

use super::*;

pub(crate) struct Enum;

impl Form for Enum {
    type Item = syn::ItemEnum;

    fn bitwise(
        expected_width: Option<usize>,
        item: Self::Item,
    ) -> Result<Output<Self::Item>, Error> {
        check_generics(item.generics)?;

        let mut from_repr_checked_arms = vec![];

        let max_discrim: Option<usize> = None;
        for variant in item.variants.iter() {
            if !variant.fields.is_empty() {
                return Err(err!(variant.fields.span(); "variant fields are not supported"));
            }

            let variant_span = variant.span();

            let pat;
            if let Some((_, discrim)) = variant.discriminant {
                let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(lit ), .. }) = discrim else {
                    return Err(err!(discrim.span(); "variant discriminant must be an integer literal"));
                };
                max_discrim = Some(lit.base10_parse().map_err(Error::new)?);
                pat = syn::PatLit { attrs: vec![], lit: lit.into() }.into();
            } else {
                let discrim = max_discrim.map(|it| it + 1).unwrap_or(0);
                pat = syn::PatLit {
                    attrs: vec![],
                    lit: syn::LitInt::new(&discrim.to_string(), variant_span).into(),
                }
                .into();
                max_discrim = Some(discrim);
            }

            from_repr_checked_arms.push(syn::Arm {
                attrs: vec![],
                pat,
                guard: None,
                fat_arrow_token: syn::Token![=>](variant_span),
                body: Box::new(syn::ExprCall {
                    attrs: vec![],
                    func: Box::new(syn::ExprPath {
                        attrs: vec![],
                        qself: None,
                        path: path!(variant_span; :: core option Option Some),
                    }.into()),
                    paren_token: syn::token::Paren(variant_span),
                    args: once(syn::Expr::Path(syn::ExprPath {
                        attrs: vec![],
                        qself: None,
                        path: syn::Path {
                            leading_colon: None,
                            segments: [syn::Ident::new("Self", variant_span), variant.ident]
                                .into_iter()
                                .map(syn::PathSegment::from)
                                .collect(),
                        }
                    })).collect(),
                }.into()),
                comma: Some(syn::Token![,](variant_span)),
            });
        }

        let item_span = item.span();

        let max_discrim = max_discrim.ok_or_else(|| err!(item_span; "enum cannot have zero variants"))?;
        let mut item_width = 1;
        if max_discrim != 0 {
            item_width += usize::try_from(max_discrim.ilog2()).unwrap();
        }
        let item_width = Width::Met(item_span, item_width);

        let item_repr = uint::RustType::repr_for_item(expected_width, &item_width, &mut item.attrs)?;
        item.attrs.push(syn::Attribute {
            pound_token: syn::Token![#](item_span),
            style: syn::AttrStyle::Outer,
            bracket_token: syn::token::Bracket(item_span),
            meta: syn::MetaList {
                path: syn::Ident::new("repr", item_span).into(),
                delimiter: syn::MacroDelimiter::Paren(syn::token::Paren(item_span)),
                tokens: item_repr.into_syn_type(item_span).into_token_stream(),
            }
            .into(),
        });

        let mut const_block = None;
        if let Some(expected_width) = expected_width {
            match EnforceItemWidthStrategy::devise(expected_width, item_width) {
                EnforceItemWidthStrategy::None => {},
                EnforceItemWidthStrategy::Fail(e) => {
                    return Err(e);
                }
                EnforceItemWidthStrategy::ConstCheck(expr) => {
                    const_block = Some(syn::Block {
                        brace_token: syn::token::Brace(item_span),
                        stmts: vec![syn::Stmt::Expr(expr, None)],
                    })
                }
            }
        }

        todo!()
        /*
        Output { const_block, item: item.into(), item_impl: None, bitwise_impl }
            attrs: item_attrs,
            vis: item_vis,
            token: quote!(enum),
            ident: item_ident,
            body: quote!({ #item_variants }),
            methods: vec![],
            bitwise_impl: BitwiseImpl {
                width: item_width,
                repr: item_repr,
                from_repr_unchecked: quote! {
                    // FIXME: is there a less 'wildly unsafe' version to this?
                    ::core::mem::transmute(repr)
                },
                from_repr_checked: quote! {
                    match repr as usize {
                        #(#from_repr_checked_arms,)*
                        _ => None,
                    }
                },
                to_repr: quote! {
                    // FIXME: is there an equivalent safe version?
                    unsafe { *(self as *const Self as *const _) }
                },
            },
        }
        */
    }
}
