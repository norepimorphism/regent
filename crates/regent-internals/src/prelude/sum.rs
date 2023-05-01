// SPDX-License-Identifier: MPL-2.0

//! A sum of unsigned integers that expands to a `usize` expression at compile-time.

use super::*;

/// The bit-width of a type.
pub(crate) type Width = Sum;

/// A sum of unsigned integers that expands to a `usize` expression at compile-time.
#[derive(Clone)]
pub(crate) enum Sum {
    /// An unsigned integer literal whose value is known at macro evaluation time (MET).
    Met { span: Span2, value: usize },
    /// A `usize` expression whose value is known only at compile-time (CT).
    Ct(syn::Expr),
}

impl Sum {
    /// Creates a sum from a single `0usize` literal.
    pub(crate) fn zero(span: Span2) -> Self {
        Self::Met { span, value: 0 }
    }

    /// The associated span.
    pub(crate) fn span(&self) -> Span2 {
        match self {
            Self::Met { span, .. } => *span,
            Self::Ct(inner) => inner.span(),
        }
    }

    /// Expands this sum into a [`syn::Expr`].
    pub(crate) fn into_expr(self) -> syn::Expr {
        let span = self.span();
        let expr = match self {
            Self::Met { value, .. } => syn::ExprLit {
                attrs: vec![],
                lit: syn::LitInt::new(&value.to_string(), span).into(),
            }
            .into(),
            Self::Ct(inner) => inner,
        };

        syn::ExprParen { attrs: vec![], paren_token: syn::token::Paren(span), expr: Box::new(expr) }
            .into()
    }

    /// Adds the given sum to this sum.
    pub(crate) fn add(&mut self, rhs: Self) {
        match (self, rhs) {
            (Self::Met { value: lhs, .. }, Self::Met { value: rhs, .. }) => {
                *lhs += rhs;
            }
            (_, _) => {
                *self = Self::Ct(
                    syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(self.into_expr()),
                        op: syn::BinOp::Add(syn::Token![+](self.span())),
                        right: Box::new(rhs.into_expr()),
                    }
                    .into(),
                );
            }
        }
    }
}
