// SPDX-License-Identifier: MPL-2.0

//! The `bitwise` macro for enums.

use super::*;

pub(crate) struct Enum;

impl Form for Enum {
    type Item = syn::ItemEnum;

    fn bitwise(mut item: Self::Item) -> Result<Output<Self::Item>> {
        // For the enum form of `bitwise`, we need to do two things:
        //
        // - add a `#[repr]` outer attribute to the item if not present already
        // - generate the `Bitwise` implementation for the item
        //
        // This list is quite short. In fact, we do not modify the item at all except for the
        // `#[repr]` attribute, and as for the `Bitwise` implementation, all but one of the
        // associated functions can be generated without inspecting the item. The exception is
        // `from_repr_checked`, which requires us to know all of the enum variants and their
        // discriminants.
        //
        // The meat of `Enum::bitwise` is iterating over the enum variants, calculating their
        // discriminants in the process, and using this information to build a match expression for
        // `from_repr_checked` that assigns each bit-pattern allowed by the enum representation a
        // `Some(variant)` or `None`.

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
                    return Err(err!(span; "variant discriminant must be an unsigned integer literal"));
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
            // Rendered:
            //   ::core::option::Option::Some(Self::#ident)
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
            // Rendered:
            //   #discrim_lit => #match_arm_rhs,
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

        // This corresponds to `Output::const_ctx`.
        let mut const_ctx = vec![];
        let mut has_repr_attr = false;
        // This is the internal representation, or storage type, of the emitted item.
        let item_repr = uint::RustType::repr_for_item(
            item_span,
            &item.ident,
            &item_width,
            &mut item.attrs,
            &mut const_ctx,
            |_, _| {
                has_repr_attr = true;
            },
        )?;
        // Add a `#[repr]` attribute if there isn't one already.
        if !has_repr_attr {
            // Rendered:
            //   #[repr(#item_repr)]
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
        // Rendered:
        //   ::core::mem::transmute(repr)
        let from_repr_unchecked = syn::ExprCall {
            attrs: vec![],
            func: Box::new(expr_path!(item_span; ::core::mem::transmute)),
            paren_token,
            args: once::<syn::Expr>(expr_path!(item_span; repr)).collect(),
        };

        // This cryptically-named boolean expresses whether there is a one-to-one correspondence
        // between the set of discriminants in this enum and the set of bit-patterns allowed by
        // `item_repr`. In other words, this describes whether the enum 'fills' its representation
        // or not.
        //
        // We can prove this informally by observing that:
        //
        // - The discriminants are guaranteed to be values of the representation type (because the
        //   enum has a `#[repr]` attribute)
        // - Hence, the possible values of the discriminants range from 0 to the maximum value
        //   allowed by the representation
        // - Any two variants cannot share the same discriminant (the compiler does not allow this)
        //
        // Therefore, if the number of discriminants (or equivalently, the number of variants) is
        // equal to the number of unique bit-patterns allowed by the representation (given by
        // `pow(2, width)`), then the enum is isomorphic with its representation. If this is the
        // case, we can replace our lengthy match expression with a call to `mem::transmute`.
        // Otherwise, we must use a wildcard match arm.
        let is_isomorphic_with_repr = 2usize.pow(item_repr.width() as _) == item.variants.len();

        // This is the `from_repr_checked` method.
        let from_repr_checked = if is_isomorphic_with_repr {
            // We no longer need this.
            drop(from_repr_checked_arms);

            // Rendered:
            //   { ::core::option::Option::Some(#from_repr_unchecked) }
            blockify(syn::ExprCall {
                attrs: vec![],
                func: Box::new(expr_path!(item_span; ::core::option::Option::Some)),
                paren_token,
                args: once(syn::Expr::from(from_repr_unchecked.clone())).collect(),
            })
        } else {
            let span = item.variants.span();
            // Rendered:
            //   _ => ::core::option::Option::None,
            let wildcard_arm = syn::Arm {
                attrs: vec![],
                pat: syn::PatWild { attrs: vec![], underscore_token: syn::Token![_](span) }.into(),
                guard: None,
                fat_arrow_token: syn::Token![=>](span),
                body: Box::new(expr_path!(span; ::core::option::Option::None)),
                comma: Some(syn::Token![,](span)),
            };
            from_repr_checked_arms.push(wildcard_arm);

            // Rendered:
            //   { match repr { #from_repr_checked_arms } }
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
        // Rendered:
        //   { unsafe { ::core::ptr::read(self as *const Self as *const _) } }
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

            // Rendered:
            //   self as *const Self
            let self_as_const_self = syn::ExprCast {
                attrs: vec![],
                expr: Box::new(expr_path!(item_span; self)),
                as_token,
                ty: Box::new(make_const_ptr(ty_path!(item_span; Self))),
            }
            .into();
            // Rendered:
            //   #self_as_const_self as *const _
            let self_as_const_infer = syn::ExprCast {
                attrs: vec![],
                expr: Box::new(self_as_const_self),
                as_token,
                ty: Box::new(make_const_ptr(syn::TypeInfer { underscore_token }.into())),
            }
            .into();
            // Rendered:
            //   ::core::ptr::read(#self_as_const_infer)
            let ptr_read_expr = syn::ExprCall {
                attrs: vec![],
                func: Box::new(expr_path!(::core::ptr::read)),
                paren_token,
                args: once(self_as_const_infer).collect(),
            };

            syn::ExprUnsafe { attrs: vec![], unsafe_token, block: blockify(ptr_read_expr) }
        });
        // This is the `into_repr` method.
        //
        // Rendered:
        //   { self as _ }
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

        Ok(Output { const_ctx, item, impl_item: None, impl_bitwise_for_item })
    }
}
