// SPDX-License-Identifier: MPL-2.0

//! A sum of unsigned integers that expands to a `usize` expression at compile-time.

use super::*;

/// The bit-width of a type.
pub(crate) type Width = Sum;

/// A sum of unsigned integers that expands to a `usize` expression at compile-time.
#[derive(Clone)]
pub(crate) enum Sum {
    /// An unsigned integer whose value is known at macro evaluation time (MET).
    Met(Span2, usize),
    /// A `usize` expression whose value is known only at compile-time (CT).
    Ct(syn::Expr),
}

impl Sum {
    /// Creates a sum of zero with the given span.
    pub(crate) fn zero(span: Span2) -> Self {
        Self::Met(span, 0)
    }

    /// The associated span.
    pub(crate) fn span(&self) -> Span2 {
        match self {
            Self::Met(span, _) => *span,
            Self::Ct(inner) => inner.span(),
        }
    }

    /// Expands this sum into a [`syn::Expr`].
    pub(crate) fn into_expr(self) -> syn::Expr {
        match self {
            Self::Met(span, value) => syn::ExprLit {
                attrs: vec![],
                lit: syn::LitInt::new(&value.to_string(), span).into(),
            }
            .into(),
            Self::Ct(inner) => inner,
        }
    }

    /// Expands this sum into a parenthesized [`syn::Expr`].
    pub(crate) fn into_parenthesized_expr(self) -> syn::Expr {
        parenthesize(self.into_expr())
    }

    pub(crate) fn parenthesize(&mut self) {
        if let Self::Ct(expr) = self {
            *expr = parenthesize(*expr);
        }
    }
}

fn parenthesize(expr: syn::Expr) -> syn::Expr {
    syn::ExprParen { attrs: vec![], paren_token: syn::token::Paren(expr.span()), expr: Box::new(expr) }
        .into()
}
