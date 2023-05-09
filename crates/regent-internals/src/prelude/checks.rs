// SPDX-License-Identifier: MPL-2.0

//! Checks to be performed at macro evaluation time or compile-time.

use super::*;

/// Returns an [`Error`] if the given [`syn::Generics`] is non-empty.
///
/// The `bitwise` macro does not support generic items. This function ensures that the current item
/// is not generic.
///
/// `generics` is passed by-value to discourage its use after this function is called.
pub(crate) fn check_generics(generics: syn::Generics) -> Result<(), Error> {
    let syn::Generics { params, where_clause, .. } = generics;
    if !params.is_empty() {
        return Err(err!(params.span(); "generics parameters are not supported in this context"));
    }
    if let Some(clause) = where_clause {
        return Err(err!(clause.span(); "`where` clauses are not supported in this context"));
    }

    Ok(())
}

/// A strategy to enforce the expected bit-width of an item.
pub(crate) enum EnforceItemWidthStrategy {
    /// The expected width is correct, and nothing needs to be done.
    None,
    /// The expected width is incorrect, and this error should be returned during macro evaluation.
    Fail(Error),
    /// The correctness of the expected width is indeterminate at macro evaluation time, so this
    /// expression should be inserted in a const context to perform the check at compile-time.
    ConstCheck(syn::Expr),
}

impl EnforceItemWidthStrategy {
    /// Devises an `EnforceItemWidthStrategy`.
    ///
    /// The `bitwise` macro accepts `size` and `width` attribute arguments which are intended to
    /// make compile-time guarantees about the `Bitwise::WIDTH` of the emitted item. In the simple
    /// case, the width is calculated exactly during macro evaluation and an error is returned if it
    /// differs from `expected_width`. Otherwise, if the item is a struct containing custom
    /// implementors of`Bitwise`, the exact width is indeterminate at macro evaluation time and so
    /// enforcement of `expected_width` is deferred to compile-time via an assertion in a const
    /// context.
    pub(crate) fn devise(expected_width: usize, actual_width: Width) -> Self {
        match actual_width {
            Width::Met(span, actual_width) => {
                if expected_width != actual_width {
                    return Self::Fail(err!(
                        span;
                        "item width is {actual_width} bits, should be {expected_width}",
                    ));
                }
            }
            Width::Ct(_) => {
                // We don't have enough information to evaluate `actual_width` at macro evaluation
                // time, but we can emit Rust code to do so at compile-time.
                return Self::const_check(expected_width, actual_width);
            }
        }

        Self::None
    }

    /// Devises a 'const check' strategy.
    ///
    /// This produces an expression of the form:
    ///
    /// ```no_run
    /// if #expected_width != #actual_width {
    ///     ::core::panicking::panic(/* panic message */);
    /// }
    /// ```
    fn const_check(expected_width: usize, actual_width: Width) -> Self {
        let span = actual_width.span();

        let panic_path = syn::Path {
            leading_colon: Some(syn::Token![::](span)),
            segments: ["core", "panicking", "panic"]
                .into_iter()
                .map(|it| syn::PathSegment::from(syn::Ident::new(it, span)))
                .collect(),
        };
        let panic_arg = syn::Expr::Lit(syn::ExprLit {
            attrs: vec![],
            // FIXME: print item ident so the user knows that the heck we're talking about
            lit: syn::LitStr::new(&format!("item width should be {expected_width}"), span).into(),
        });
        let panic_stmt = syn::Stmt::Expr(
            syn::ExprCall {
                attrs: vec![],
                func: Box::new(
                    syn::ExprPath { attrs: vec![], qself: None, path: panic_path }.into(),
                ),
                paren_token: syn::token::Paren(span),
                args: once(panic_arg).collect(),
            }
            .into(),
            Some(syn::Token![;](span)),
        );

        let expected_width = syn::ExprLit {
            attrs: vec![],
            lit: syn::LitInt::new(&expected_width.to_string(), span).into(),
        }
        .into();
        let condition = syn::ExprBinary {
            attrs: vec![],
            left: Box::new(expected_width),
            op: syn::BinOp::Ne(syn::Token![!=](span)),
            right: Box::new(actual_width.into_expr()),
        }
        .into();

        Self::ConstCheck(
            syn::ExprIf {
                attrs: vec![],
                if_token: syn::Token![if](span),
                cond: Box::new(condition),
                then_branch: syn::Block {
                    brace_token: syn::token::Brace(span),
                    stmts: vec![panic_stmt],
                },
                else_branch: None,
            }
            .into(),
        )
    }
}
