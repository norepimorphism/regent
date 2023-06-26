// SPDX-License-Identifier: MPL-2.0

//! Bitfields in Rust.
//!
//! *regent* is a Rust crate for making bitfield structures. The sole API is the attribute macro
//! [`bitwise!`], which generates a struct of tightly packed, arbitrarily wide fields with
//! accompanying constructors and accessor methods.
//!
//! # ⚠️ Notice
//!
//! If you haven't done so already, it is highly recommended to consult [the README] for a primer on
//! Regent; crate documentation hereafter assumes an understanding of the concepts established
//! there. A semi-formal specification of `#[bitwise]` is also available in the [`spec`] module of
//! this crate.
//!
//! [the README]: https://github.com/norepimorphism/regent#readme

#![no_std]

pub mod spec;

pub use regent_internals::bitwise;

/// The trait automatically implemented for items emitted by the [`bitwise!`] macro.
///
/// This trait
/// - exposes compile-time information about the implementor, including its [field-width] and
///   [representation]; and
/// - provides conversion routines between the implementor and its representation.
///
/// > You should not need to implement this trait manually. If `#[bitwise]` does not support a kind
/// of item you think it should, please submit an issue to [the GitHub repository]. Thanks!
///
/// # Conversions
///
/// Converting a value of the implementor into its representation is done with [`to_repr`] and
/// [`into_repr`]. `to_repr` borrows `self` whereas `into_repr` induces a move.
///
/// ```ignore
/// fn take_implementor(implementor: impl Bitwise) {
///     // Pass `implementor` by reference.
///     use_repr(implementor.to_repr());
///     // Pass `implementor` by move.
///     use_repr(implementor.into_repr());
///
///     // error[E0382]: use of moved value: `implementor`
///     // use_repr(implementor.to_repr());
///     // error[E0382]: use of moved value: `implementor`
///     // use_repr(implementor.into_repr());
/// }
///
/// fn use_repr<Repr>(_: Repr) {}
/// ```
///
/// The inverse operation&mdash;constructing a value of the implementor from a
/// representation&mdash;is done with [`from_repr`].
///
/// [field-width]: Self::FIELD_WIDTH
/// [`from_repr`]: Self::from_repr
/// [`into_repr`]: Self::into_repr
/// [representation]: Self::Repr
/// [the GitHub repository]: https://github.com/norepimorphism/regent
/// [`to_repr`]: Self::to_repr
pub trait Bitwise: Sized {
    /// The width of a bitfield whose type is the implementor.
    ///
    /// For structs, this is the sum of the widths of all constituent fields. For enums, this is the
    /// minimum number of bits necessary to encode all possible discriminants.
    ///
    /// This quantity is distinguished from [`REPR_WIDTH`], which is the bit-width of [the
    /// representation].
    ///
    /// [`REPR_WIDTH`]: BitwiseExt::REPR_WIDTH
    /// [the representation]: Self::Repr
    const FIELD_WIDTH: usize;

    /// The unsigned integer primitive used to represent a value of the implementor in-memory.
    ///
    /// If the implementor is decorated with a `#[repr]` attribute, this type is its argument.
    /// Otherwise, this is the unsigned integer primitive of width [`FIELD_WIDTH`] rounded up to the
    /// next-greatest power of two.
    ///
    /// [`FIELD_WIDTH`]: Self::FIELD_WIDTH
    type Repr;

    /// The implementor of [`Fallible`] returned by the [`from_repr`] method.
    ///
    /// [`from_repr`]: Self::from_repr
    type FromReprFallible: Fallible<Output = Self>;

    /// Constructs a value of the implementor from a [representation].
    ///
    /// # [Error-handling](Fallible)
    ///
    /// An error occurs if the `repr` argument does not constitute a valid bit-pattern for the
    /// implementor. For structs, this means that one or more bits in the representation that are
    /// not inhabited by fields are non-zero, or that the bit-ranges inhabited by one or more
    /// constant fields do not constitute the correct values for the constants. For enums, this
    /// means that the bit-range uninhabited by the discriminant is non-zero.
    ///
    /// Behavior of the various error-handling strategies offered by [`Fallible`] is described in
    /// the following sections.
    ///
    /// ## [Panicking](Fallible::panicking)
    ///
    /// Panics with a message explaining why `repr` is not a valid bit-pattern for the implementor.
    ///
    /// ## [Masked](Fallible::masked)
    ///
    /// Safely and silently ignores the error.
    ///
    /// ## [Checked](Fallible::checked)
    ///
    /// Returns `None`.
    ///
    /// ## [Unchecked](Fallible::unchecked)
    ///
    /// This is semantically equivalent to [`transmute`], and the same invariants apply.
    ///
    /// [representation]: Self::Repr
    /// [`transmute`]: core::mem::transmute
    fn from_repr(repr: Self::Repr) -> Self::FromReprFallible;

    /// Converts this into a value of its [representation] without moving.
    ///
    /// [representation]: Self::Repr
    #[must_use]
    fn to_repr(&self) -> Self::Repr;

    /// Converts this into a value of its [representation] by-move.
    ///
    /// [representation]: Self::Repr
    #[must_use]
    fn into_repr(self) -> Self::Repr;
}

/// An extension to the [`Bitwise`] trait that is automatically implemented for implementors
/// thereof.
pub trait BitwiseExt: Bitwise {
    /// The bit-width of the [representation] type.
    ///
    /// This is eight times the size, in bytes, of `Bitwise::Repr`.
    ///
    /// [representation]: Bitwise::Repr
    const REPR_WIDTH: usize;
}

impl<T: Bitwise> BitwiseExt for T {
    const REPR_WIDTH: usize = 8 * core::mem::size_of::<Self::Repr>();
}

/// A fallible operation involving an implementor of [`Bitwise`].
///
/// Conceptually, `Fallible<Output>` is like `impl FnOnce(Args) -> Output` except that
/// calling a `Fallible` may fail. In case of failure, four different error-handling
/// strategies are available, each corresponding to a method that consumes `self`:
///
/// - [`panicking`](Self::panicking)
/// - [`masked`](Self::masked)
/// - [`checked`](Self::checked)
/// - [`unchecked`](Self::unchecked)
#[must_use = "a `Fallible` operation does not execute until you call one of `panicking()`, \
`masked()`, `checked()`, or `unchecked()`"]
pub trait Fallible {
    type Output;

    fn panicking(self) -> Self::Output;
    fn masked(self) -> Self::Output;
    fn checked(self) -> Option<Self::Output>;
    unsafe fn unchecked(self) -> Self::Output;
}

/// An opaque wrapper around `T`.
#[repr(transparent)]
pub struct Opaque<T>(T);
