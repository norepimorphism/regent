// SPDX-License-Identifier: MPL-2.0

//! A documentation-only module that explains how to use [`bitwise`].
//!
//! [`bitwise`]: crate::bitwise
//!
//! This module is dedicated to describing the syntax and behavior of the `bitwise` attribute macro.
//! Supporting items exported by Regent, including the [`Bitwise`] and [`BitwiseExt`] traits, are
//! documented separately.
//!
//! [`Bitwise`]: crate::Bitwise
//! [`BitwiseExt`]: crate::BitwiseExt
//!
//! `bitwise` can be applied to struct and enum items. The interface and behavior of the macro
//! depends on the kind of item it receives, but in general, the output is an item of the same kind
//! as the input and implements the `Bitwise` trait.
//!
//! Each form of the `bitwise` macro is described in a separate submodule.
//!
//! ## Syntax Reference
//!
//! At macro evaluation time, `bitwise` parses the input item and validates it against its own
//! syntactical rules. This syntax is a subset of Rust syntax and is notated in a modified
//! [Augmented Backus-Naur Form] where:
//!
//! [Augmented Backus-Naur Form]: https://en.wikipedia.org/wiki/Augmented_Backus%E2%80%93Naur_form
//!
//! - implicit whitespace is allowed between concatenated rule elements (and may be required,
//!   depending on the context);
//! - literal text strings are case sensitive by default; and
//! - <code>%r"<em>rule</em>"</code> is a rule from [The Rust Reference] (and should not be
//!   interpreted as a literal text string).
//!
//! [The Rust Reference]: https://doc.rust-lang.org/reference/
//!
//! Syntactical rules common to all uses of `bitwise` are:
//!
//! ```abnf
//! item-attr = bitwise-attr / %r"OuterAttribute"
//! bitwise-attr = "#[" "bitwise" [bitwise-attr-input] "]"
//! bitwise-attr-input = "(" *(bitwise-attr-arg ",") [bitwise-attr-arg [","]] ")"
//! bitwise-attr-arg = size-arg / width-arg
//! size-arg = "size" "=" %r"INTEGER_LITERAL"
//! width-arg = "width" "=" %r"INTEGER_LITERAL"
//! ```

pub mod r#enum;
pub mod r#struct;
