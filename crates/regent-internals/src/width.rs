// SPDX-License-Identifier: MPL-2.0

//! The bit-width of a type.

use super::*;

/// The bit-width of a type. Expands to a `usize` expression at compile-time.
#[derive(Clone)]
pub(crate) enum Width {
    /// An unsigned integer whose value is known at macro evaluation time (MET).
    Met(Span2, usize),
    /// A `usize` expression whose value is known only at compile-time (CT).
    Ct(syn::Expr),
}

impl Width {
    /// Creates a width of zero with the given span.
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

    pub(crate) fn add(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (Self::Met(span, lhs), Self::Met(_, rhs)) => {
                Self::Met(span, lhs + rhs)
            }
            (lhs, rhs) => {
                let span = lhs.span();

                Self::Ct(
                    syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(lhs.into_expr()),
                        op: syn::BinOp::Add(syn::Token![+](span)),
                        right: Box::new(rhs.into_expr()),
                    }
                    .into()
                )
            }
        }
    }

    /// Expands this into a [`syn::Expr`].
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

    /// Expands this into a parenthesized [`syn::Expr`].
    pub(crate) fn into_parenthesized_expr(self) -> syn::Expr {
        parenthesize(self.into_expr())
    }
}

fn parenthesize(expr: syn::Expr) -> syn::Expr {
    syn::ExprParen {
        attrs: vec![],
        paren_token: syn::token::Paren(expr.span()),
        expr: Box::new(expr),
    }
    .into()
}
