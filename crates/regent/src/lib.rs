// SPDX-License-Identifier: MPL-2.0

#![no_std]

pub mod spec;

pub use regent_internals::bitwise;

pub trait Bitwise: Sized {
    /// The 'exact' bit-width of this type.
    ///
    /// For structs, this is the sum of the widths of all constituent fields. For enums, this is the
    /// minimum width necessary to encode all possible variants.
    const WIDTH: usize;

    /// The unsigned integer primitive that represents this type in-memory.
    type Repr;

    unsafe fn from_repr_unchecked(repr: Self::Repr) -> Self;

    fn from_repr_checked(repr: Self::Repr) -> Option<Self>;

    fn to_repr(&self) -> Self::Repr;

    fn into_repr(self) -> Self::Repr;
}

pub trait BitwiseExt: Bitwise {
    /// The bit-width of this type in memory.
    ///
    /// This is eight times the size, in bytes, of [`Repr`](Bitwise::Repr).
    const REPR_WIDTH: usize;
}

impl<T: Bitwise> BitwiseExt for T {
    const REPR_WIDTH: usize = 8 * core::mem::size_of::<Self::Repr>();
}
