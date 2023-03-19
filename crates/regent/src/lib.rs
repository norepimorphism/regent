// SPDX-License-Identifier: MPL-2.0

pub use regent_internals::bitwise;

pub trait Bitwise {
    const WIDTH: usize;
    const REPR_WIDTH: usize = 8 * std::mem::size_of::<Self::Repr>();

    type Repr;
}
