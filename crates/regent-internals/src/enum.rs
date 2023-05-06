// SPDX-License-Identifier: MPL-2.0

//! The `bitwise` macro for enums.

use crate::prelude::*;

/// The `bitwise` macro for enums.
pub fn bitwise(expected_width: Option<usize>, item: syn::ItemEnum) -> Result<Output, Error> {
    check_generics(item.generics)?;
    let item_span = item.span();
    let syn::ItemEnum {
        attrs: mut item_attrs,
        ident: item_ident,
        enum_token: item_enum,
        variants: item_variants,
        vis: item_vis,
        ..
    } = item;

    let mut from_repr_checked_arms = vec![];
    let mut next_discrim = Width::Lit(0);
    for variant in item_variants.iter() {
        check_variant_fields(variant.fields)?;

        let variant_ident = &variant.ident;
        let variant_span = variant_ident.span();

        let variant_discrim = if let Some((_, discrim)) = &variant.discriminant {
            Width::Expr(discrim.clone())
        } else {
            next_discrim.clone()
        };
        from_repr_checked_arms.push(quote!(#variant_discrim => Some(Self::#variant_ident)));
        next_discrim = variant_discrim + Width::Lit(1);
    }

    let item_width = Width::Lit(match item_variants.len() {
        1 => 1,
        other if other.is_power_of_two() => other.ilog2() as _,
        other => (other.ilog2() + 1) as _,
    });

    let mut const_ctx = vec![];
    enforce_item_width!(expected_width, item_span, item_width, const_ctx);
    let item_repr =
        unwrap!(determine_item_repr(expected_width, item_span, &mut item_attrs, &item_width));
    item_attrs.push({
        let dont_care_span = Span2::call_site();

        syn::Attribute {
            pound_token: syn::Token![#](dont_care_span),
            style: syn::AttrStyle::Outer,
            bracket_token: syn::token::Bracket(dont_care_span),
            meta: syn::MetaList {
                path: syn::Ident::new("repr", dont_care_span).into(),
                delimiter: syn::MacroDelimiter::Paren(syn::token::Paren(dont_care_span)),
                tokens: item_repr.into_token_stream(),
            }
            .into(),
        }
    });

    let mut output = Item {
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
    .into_token_stream();
    output.extend(prelude);

    output.into()
}

fn check_variant_fields(fields: syn::Fields) -> Result<(), Error> {
    if fields.is_empty() {
        return Err(err!(fields.span(); "variant fields are not supported"));
    }

    Ok(())
}
