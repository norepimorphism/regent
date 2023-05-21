// SPDX-License-Identifier: MPL-2.0

//! The `bitwise` macro for enums.

use super::*;

pub(crate) struct Enum;

impl Form for Enum {
    type Item = syn::ItemEnum;

    fn bitwise(mut item: Self::Item) -> Result<Output<Self::Item>> {
        check_generics(&item.generics)?;

        // These are the arms of the match expression used to implement
        // `Bitwise::from_repr_checked`.
        let mut from_repr_checked_arms: Vec<syn::Arm> = vec![];
        // This is the greatest-valued enum discriminant. Later, we will use this to compute the
        // bit-width of the emitted item.
        //
        // This is an `Option` (for now) due to the possibility of a zero-variant enum.
        let mut max_discrim: Option<usize> = None;

        for variant in item.variants.iter() {
            if !variant.fields.is_empty() {
                return Err(err!(variant.fields.span(); "variant fields are not supported"));
            }

            let span = variant.span();

            // `discrim` is the discriminant of this variant as a `usize`, and `discrim_lit` is the
            // discriminant as a `syn::LitInt`.
            //
            // If the user explicitly specifies a discriminant, we will use that. Otherwise, the
            // discriminant will be one greater than the last (or zero if this is the first
            // variant).
            let (discrim, discrim_lit) = if let Some((_, expr)) = &variant.discriminant {
                let span = expr.span();
                let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(lit ), .. }) = expr else {
                    return Err(err!(span; "variant discriminant must be an integer literal"));
                };
                let discrim = lit.base10_parse().map_err(Error)?;

                (discrim, lit.clone())
            } else {
                let discrim = max_discrim.map(|it| it + 1).unwrap_or(0);

                (discrim, syn::LitInt::new(&discrim.to_string(), span))
            };
            // Update `max_discrim` before we forget.
            max_discrim = Some(discrim);

            // Now, we construct a match arm for `from_repr_checked_arms`.

            let match_arm_lhs = syn::PatLit { attrs: vec![], lit: discrim_lit.into() }.into();
            let match_arm_rhs = syn::ExprCall {
                attrs: vec![],
                func: Box::new(expr_path!(span; ::core::option::Option::Some)),
                paren_token: syn::token::Paren(span),
                args: once(syn::Expr::Path(syn::ExprPath {
                    attrs: vec![],
                    qself: None,
                    path: syn::Path {
                        leading_colon: None,
                        segments: [syn::Ident::new("Self", span), variant.ident.clone()]
                            .into_iter()
                            .map(syn::PathSegment::from)
                            .collect(),
                    },
                }))
                .collect(),
            }
            .into();
            // This looks like:
            //   #discrim_lit => ::core::option::Option::Some(Self::#ident),
            let match_arm = syn::Arm {
                attrs: vec![],
                pat: match_arm_lhs,
                guard: None,
                fat_arrow_token: syn::Token![=>](span),
                body: Box::new(match_arm_rhs),
                comma: Some(syn::Token![,](span)),
            };
            from_repr_checked_arms.push(match_arm);
        }

        let max_discrim = max_discrim
            .ok_or_else(|| err!(item.brace_token.span.join(); "enum cannot have zero variants"))?;
        // This is the computed bit-width of the emitted item.
        //
        // In the case of an enum, the bit-width is the minimum number of bits required to represent
        // the maximum discriminant, `max_discrim`. In particular, if `max_discrim` is 0, the
        // bit-width is 1, and if `max_discrim` is greater than 0, the bit-width is 1 plus the
        // (floored) base-2 logarithm of `max_discrim`. (I will not provide a proof of this.)
        let mut item_width = 1;
        if max_discrim > 0 {
            item_width += usize::try_from(max_discrim.ilog2()).unwrap();
        }

        let item_span = item.span();
        let item_width = Width::Met(item_span, item_width);

        let mut has_repr_attr = false;
        // This is the internal representation, or storage type, of the emitted item.
        let item_repr =
            uint::RustType::repr_for_item(item_span, &item_width, &mut item.attrs, |_, _| {
                has_repr_attr = true;
            })?;
        // Add a `#[repr]` attribute if there isn't one already.
        if !has_repr_attr {
            item.attrs.push(syn::Attribute {
                pound_token: syn::Token![#](item_span),
                style: syn::AttrStyle::Outer,
                bracket_token: syn::token::Bracket(item_span),
                meta: syn::MetaList {
                    path: path!(item_span; repr),
                    delimiter: syn::MacroDelimiter::Paren(syn::token::Paren(item_span)),
                    tokens: item_repr.into_syn_type(item_span).into_token_stream(),
                }
                .into(),
            });
        }

        // We are now ready to build the `Output` type.

        let as_token = syn::Token![as](item_span);
        let brace_token = syn::token::Brace(item_span);
        let const_token = syn::Token![const](item_span);
        let match_token = syn::Token![match](item_span);
        let paren_token = syn::token::Paren(item_span);
        let star_token = syn::Token![*](item_span);
        let underscore_token = syn::Token![_](item_span);
        let unsafe_token = syn::Token![unsafe](item_span);

        // This is the `from_repr_unchecked` method.
        //
        // This looks like:
        //   ::core::mem::transmute(repr)
        let from_repr_unchecked = syn::ExprCall {
            attrs: vec![],
            func: Box::new(expr_path!(item_span; ::core::mem::transmute)),
            paren_token,
            args: once::<syn::Expr>(expr_path!(item_span; repr)).collect(),
        };

        // This cryptically-named boolean expresses whether there is a one-to-one correspondence
        // between the set of discriminants in this enum and the set of values allowed by
        // `item_repr`. In other words, this describes whether the enum 'fills' its representation
        // or not.
        let is_isomorphic_with_repr = 2usize.pow(item_repr.width() as _) == item.variants.len();
        // This is the `from_repr_checked` method.
        let from_repr_checked = if is_isomorphic_with_repr {
            // We can reuse `from_repr_unchecked` because all values allowed by the representation
            // correspond to variants in the enum.

            // Oops---that was a waste.
            drop(from_repr_checked_arms);

            // ::core::option::Option::Some(#from_repr_unchecked)
            blockify(syn::ExprCall {
                attrs: vec![],
                func: Box::new(expr_path!(item_span; ::core::option::Option::Some)),
                paren_token,
                args: once(syn::Expr::from(from_repr_unchecked.clone())).collect(),
            })
        } else {
            let span = item.variants.span();
            // _ => ::core::option::Option::None,
            let wildcard_arm = syn::Arm {
                attrs: vec![],
                pat: syn::PatWild { attrs: vec![], underscore_token: syn::Token![_](span) }.into(),
                guard: None,
                fat_arrow_token: syn::Token![=>](span),
                body: Box::new(expr_path!(span; ::core::option::Option::None)),
                comma: Some(syn::Token![,](span)),
            };
            from_repr_checked_arms.push(wildcard_arm);

            // match repr { #from_repr_checked_arms }
            blockify(syn::ExprMatch {
                attrs: vec![],
                match_token,
                expr: Box::new(expr_path!(item_span; repr)),
                brace_token,
                arms: from_repr_checked_arms,
            })
        };
        let from_repr_unchecked = blockify(from_repr_unchecked);

        // This is the `to_repr` method.
        //
        // This looks like:
        //   unsafe { *(self as *const Self as *const _) }
        let to_repr = blockify({
            // This closure produces a `syn::Type` of the form `*const #elem`.
            let make_const_ptr = |elem| {
                syn::TypePtr {
                    star_token,
                    const_token: Some(const_token),
                    mutability: None,
                    elem: Box::new(elem),
                }
                .into()
            };

            let self_as_const_self = syn::ExprCast {
                attrs: vec![],
                expr: Box::new(expr_path!(item_span; self)),
                as_token,
                ty: Box::new(make_const_ptr(ty_path!(item_span; Self))),
            }
            .into();
            let self_as_const_infer = syn::ExprCast {
                attrs: vec![],
                expr: Box::new(self_as_const_self),
                as_token,
                ty: Box::new(make_const_ptr(syn::TypeInfer { underscore_token }.into())),
            };
            let deref_expr = syn::ExprUnary {
                attrs: vec![],
                op: syn::UnOp::Deref(star_token),
                expr: Box::new(parenthesize(self_as_const_infer)),
            };

            syn::ExprUnsafe { attrs: vec![], unsafe_token, block: blockify(deref_expr) }
        });
        // This is the `into_repr` method.
        //
        // This looks like:
        //   self as _
        let into_repr = blockify(syn::ExprCast {
            attrs: vec![],
            expr: Box::new(expr_path!(item_span; self)),
            as_token,
            ty: Box::new(syn::TypeInfer { underscore_token }.into()),
        });

        let impl_bitwise_for_item = BitwiseImpl {
            ident: item.ident.clone(),
            width: item_width,
            repr: item_repr,
            funcs: BitwiseFuncs { from_repr_unchecked, from_repr_checked, to_repr, into_repr },
        };

        Ok(Output { item, impl_item: None, impl_bitwise_for_item })
    }
}
