// SPDX-License-Identifier: MPL-2.0

//! A documentation-only module describing the enum form of [`bitwise`].
//!
//! [`bitwise`]: crate::bitwise
//!
//! ## Syntax
//!
//! ```abnf
//! enum-item = 1*item-attr %r"Visibility" "enum" %r"IDENTIFIER" enum-body
//! enum-body = "{" *(variant ",") [variant [","]] "}"
//! ; Note: variants cannot contain fields. Discriminants, if present, must be integer literals.
//! variant = %r"IDENTIFIER" ["=" 1*%r"DEC_DIGIT"]
//! ```
//!
//! ## Semantics
//!
//! ## Output
//!
//! This form of `bitwise` produces two items:
//!
//! - An `enum` definition.
//! - An `impl ::regent::Bitwise` block implementing the `Bitwise` trait for the enum.
