// SPDX-License-Identifier: MPL-2.0

//! The bit-width of a type.

use super::*;

/// The bit-width of a type.
///
/// In some cases&mdash;such as an enum, or a struct with only `bool` or unsigned integer
/// fields&mdash;a type's width can be calculated exactly at macro evaluation time (MET). In other
/// cases, the width depends on information available only at compile-time (CT) of the crate
/// invoking [`bitwise`].
///
/// The `Width` enum encapsulates both of those possibilities in a unified interface. The most
/// important method is [`into_expr`](Self::into_expr), which converts a `Width` into a
/// [`syn::Expr`] that evaluates to a `usize` at compile-time.
///
/// This type is [spanned](Span2). The associated span can be obtained from the [`span`](Self::span)
/// method.
#[derive(Clone)]
pub(crate) enum Width {
    /// A width known at macro evaluation time (MET).
    Met(Span2, usize),
    /// A width that depends on compile-time (CT) information.
    Ct(syn::Expr),
}

impl Width {
    /// The associated span.
    pub(crate) fn span(&self) -> Span2 {
        match self {
            Self::Met(span, _) => *span,
            Self::Ct(expr) => expr.span(),
        }
    }

    /// Adds two `Width`s together.
    ///
    /// The span of `lhs` becomes the span of the result.
    pub(crate) fn add(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (Self::Met(span, lhs), Self::Met(_, rhs)) => Self::Met(span, lhs + rhs),
            (lhs, rhs) => {
                let span = lhs.span();
                let expr = syn::ExprBinary {
                    attrs: vec![],
                    left: Box::new(lhs.into()),
                    op: syn::BinOp::Add(syn::Token![+](span)),
                    right: Box::new(rhs.into()),
                }
                .into();

                Self::Ct(expr)
            }
        }
    }

    /// Multiplies two `Width`s together.
    ///
    /// The span of `lhs` becomes the span of the result.
    pub(crate) fn mul(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (Self::Met(span, lhs), Self::Met(_, rhs)) => Self::Met(span, lhs * rhs),
            (lhs, rhs) => {
                let span = lhs.span();
                let expr = syn::ExprBinary {
                    attrs: vec![],
                    left: Box::new(lhs.into()),
                    op: syn::BinOp::Mul(syn::Token![*](span)),
                    right: Box::new(rhs.into()),
                }
                .into();

                Self::Ct(expr)
            }
        }
    }

    /// Wraps the inner expression in parentheses.
    ///
    /// This function only has in effect if this `Width` is [`Ct`](Self::Ct).
    pub(crate) fn parenthesize(self) -> Self {
        match self {
            Self::Ct(expr) => Self::Ct(
                syn::ExprParen {
                    attrs: vec![],
                    paren_token: syn::token::Paren(expr.span()),
                    expr: Box::new(expr),
                }
                .into()
            ),
            it => it,
        }
    }
}

impl From<Width> for syn::Expr {
    fn from(width: Width) -> Self {
        match width {
            Width::Met(span, value) => syn::ExprLit {
                attrs: vec![],
                lit: syn::LitInt::new(&value.to_string(), span).into(),
            }
            .into(),
            Width::Ct(expr) => expr,
        }
    }
}
