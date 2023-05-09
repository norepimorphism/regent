// SPDX-License-Identifier: MPL-2.0

//! A documentation-only module describing the struct form of [`bitwise`].
//!
//! [`bitwise`]: crate::bitwise
//!
//! ## Syntax
//!
//! ```abnf
//! struct-item = 1*item-attr %r"Visibility" "struct" %r"IDENTIFIER" struct-body
//! ; Note: both normal structs and tuple structs are supported.
//! struct-body = ("{" *(field ",") [field [","]] "}") / (tuple ";")
//!
//! field = *field-attr %r"Visibility" %r"IDENTIFIER" ":" type
//!
//! field-attr = constant-attr / %r"OuterAttribute"
//! constant-attr = "#[" "constant" ["=" %r"Expression" ] "]"
//!
//! ; Note: bitfields are restricted to a subset of Rust types.
//! type = elem-type / array-type / tuple-type
//! elem-type = uint-type / "bool" / %r"SimplePath"
//! uint-type = "u" 1*%r"DEC_DIGIT"
//! ; Note: the length-part must be an undecorated integer literal.
//! ; Constant expressions are not supported.
//! array-type = "[" elem-type ";" 1*%r"DEC_DIGIT" "]"
//! tuple-type = "(" *(elem-type ",") [elem-type [","]] ")"
//! ```
//!
//! ## Semantics
//!
//! ## Output
//!
//! This form of `bitwise` produces three items:
//!
//! - A `struct` definition.
//! - An `impl` block defining constructors and accessor methods for the struct.
//! - An `impl ::regent::Bitwise` block implementing the `Bitwise` trait for the struct.
