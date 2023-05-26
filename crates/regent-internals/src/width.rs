// SPDX-License-Identifier: MPL-2.0

//! The bit-width of a type.

use super::*;

/// The bit-width of a type.
///
/// In some cases&mdash;such as an enum, or a struct with only `bool` or unsigned integer
/// fields&mdash;a type's width can be calculated exactly at macro evaluation time (MET). In other
/// cases, the width depends on information available only at compile-time (CT) of the crate
/// invoking [`bitwise!`].
///
/// The `Width` enum unifies these cases under a common interface. The most important method is
/// [`into_expr`], which converts a `Width` into a [`syn::Expr`] that evaluates to a `usize` at
/// compile-time.
///
/// This type is [spanned]. The associated span can be obtained from the [`span`] method.
///
/// [`into_expr`]: Self::into_expr
/// [spanned]: Span2
/// [`span`]: Self::span
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
}

macro_rules! impl_bin_op {
    (
        docs: $docs:literal,
        ident: $ident:ident,
        op_token: $op_token:tt,
        op_name: $op_name:ident $(,)?
    ) => {
        #[doc = $docs]
        #[doc = "\n\nThe span of `lhs` becomes the span of the result."]
        pub(crate) fn $ident(lhs: Self, rhs: Self) -> Self {
            match (lhs, rhs) {
                (Self::Met(span, lhs), Self::Met(_, rhs)) => Self::Met(span, lhs $op_token rhs),
                (lhs, rhs) => {
                    let span = lhs.span();
                    let expr = syn::ExprBinary {
                        attrs: vec![],
                        left: Box::new(lhs.into()),
                        op: syn::BinOp::$op_name(syn::Token![$op_token](span)),
                        right: Box::new(rhs.into()),
                    }
                    .into();

                    Self::Ct(expr)
                }
            }
        }
    };
}

impl Width {
    impl_bin_op!(
        docs: "Adds two `Width`s together.",
        ident: add,
        op_token: +,
        op_name: Add,
    );
    impl_bin_op!(
        docs: "Subtracts one `Width` from another.",
        ident: sub,
        op_token: -,
        op_name: Sub,
    );
    impl_bin_op!(
        docs: "Multiplies two `Width`s together.",
        ident: mul,
        op_token: *,
        op_name: Mul,
    );

    /// Wraps the inner expression in parentheses.
    pub(crate) fn parenthesize(self) -> Self {
        match self {
            Self::Ct(expr) => Self::Ct(parenthesize(expr)),
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
