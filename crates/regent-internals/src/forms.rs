// SPDX-License-Identifier: MPL-2.0

mod r#enum;
mod r#struct;

pub(super) use r#enum::Enum;
pub(super) use r#struct::Struct;

use super::*;

/// Returns an [`Error`] if the given [`syn::Generics`] is non-empty.
///
/// The `bitwise` macro does not support generic items. This function ensures that the current item
/// is not generic.
fn check_generics(generics: &syn::Generics) -> Result<()> {
    let syn::Generics { params, where_clause, .. } = generics;
    if !params.is_empty() {
        return Err(err!(params.span(); "generics parameters are not supported in this context"));
    }
    if let Some(clause) = where_clause {
        return Err(err!(clause.span(); "`where` clauses are not supported in this context"));
    }

    Ok(())
}
