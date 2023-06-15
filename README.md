# ![Regent. Bitfields in Rust.](resources/logo-subtitle@0.5x.png)

[![crates.io](https://img.shields.io/crates/v/regent)](https://crates.io/crates/regent)
[![docs.rs](https://docs.rs/regent/badge.svg)](https://docs.rs/regent)
[![MPL-2.0 license](https://img.shields.io/github/license/norepimorphism/regent)](./LICENSE)

*Regent* is a pair of Rust crates for making bitfield structures. The sole API is the attribute macro `#[bitwise]`, which generates a struct of tightly packed, arbitrarily wide fields with accompanying constructors and accessor methods.

## Guided Example

<details>
<summary>
    <strong>The fastest way to learn Regent is by example.</strong> This section demonstrates a typical use case for Regent, introducing features gradually to approach a succinct and idiomatic solution. Familiarity with Rust is assumed.
</summary>
<br>

The MIPS R3000 is a 32-bit RISC microprocessor. Like many CPUs, the R3000 has a status register (SR) that holds system variables pertaining to the architecture. Here's a diagram of it:

![Diagram of the fields in a 32-bit CPU register.][r3000-sr]

> Source: [*IDT R30xx Family Software Reference Manual*][r3000-ref], published in 1994 by Integrated Device Technology, Inc.

Each system variable corresponds to a register *field*, depicted here as a rectangle. Most fields are labeled, but a few enclose the text "0"; these fields are immutable and always read zero. Above each field are the positions of its most- and least-significant bits (or just the position of the field if it is 1-bit). The bit in position 0 is the least-significant bit of the register, and bit 31 is the most significant.

With Regent, you can model the SR as:

```rust
#[regent::bitwise(width = 32)]
pub struct StatusRegister {
    pub cu3: bool,
    pub cu2: bool,
    pub cu1: bool,
    pub cu0: bool,
    #[constant]
    _26: u2,
    pub re: bool,
    #[constant]
    _23: u2,
    pub bev: bool,
    pub ts: bool,
    pub pe: bool,
    pub cm: bool,
    pub pz: bool,
    pub swc: bool,
    pub isc: bool,
    pub im: u8,
    #[constant]
    _6: u2,
    pub kuo: bool,
    pub ieo: bool,
    pub kup: bool,
    pub iep: bool,
    pub kuc: bool,
    pub iec: bool,
}
```

This looks like a Rust struct&mdash;and, syntactically speaking, it is. What's new is:

- **The `width = 32` argument to the `#[bitwise]` attribute.** This informs Regent that the widths of all struct fields should sum to 32 bits. If they do not, Regent will emit a compile-time error.
  - You can write `size = 4` instead if you prefer to specify the width in bytes.
  - It is good practice&mdash;and is, in some cases, required&mdash;to include either a `width` or `size` argument. These help catch simple mistakes like missing or duplicated fields and are visual reminders of the struct width.
- **The `#[constant]` attribute.** This marks a struct field as immutable and initializes it with a default value (in this case, 0).
  - You can also pass a custom initial value with <code>#[constant(<em>value</em>)]</code>.
- **The `u2` type**. This is an imaginary 2-bit unsigned integer type. Regent offers `u*` types for all unsigned integers 1 to 128 bits wide.

At macro evaluation time, `#[bitwise]` expands the struct to (roughly) the following. (Function bodies are omitted for brevity.)

<details>
<summary>Expanded code</summary>
<br>

```rust
pub type StatusRegister = impl StatusRegister;

trait StatusRegister: Sized {

}

#[repr(transparent)]
pub struct StatusRegister(u32);

impl StatusRegister {
    #[must_use = /* ... */]
    pub const fn new(
        cu3: bool,
        cu2: bool,
        cu1: bool,
        cu0: bool,
        re: bool,
        bev: bool,
        ts: bool,
        pe: bool,
        cm: bool,
        pz: bool,
        swc: bool,
        isc: bool,
        im: u8,
        kuo: bool,
        ieo: bool,
        kup: bool,
        iep: bool,
        kuc: bool,
        iec: bool,
    ) -> impl regent::Fallible<Output = Self> {/* ... */}

    #[must_use = /* ... */]
    pub const fn cu3(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn cu2(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn cu1(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn cu0(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    const fn _26() -> u8 { 0 }
    #[must_use = /* ... */]
    pub const fn re(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    const fn _23() -> u8 { 0 }
    #[must_use = /* ... */]
    pub const fn bev(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn ts(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn pe(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn cm(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn pz(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn swc(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn isc(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn im(&self) -> u8 {/* ... */}
    #[must_use = /* ... */]
    const fn _6() -> u8 { 0 }
    #[must_use = /* ... */]
    pub const fn kuo(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn ieo(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn kup(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn iep(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn kuc(&self) -> bool {/* ... */}
    #[must_use = /* ... */]
    pub const fn iec(&self) -> bool {/* ... */}

    #[must_use = /* ... */]
    pub const fn set_cu3(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_cu2(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_cu1(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_cu0(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_re(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_bev(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_ts(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_pe(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_cm(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_pz(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_swc(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_isc(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_im(&mut self, field: u8) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_kuo(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_ieo(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_kup(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_iep(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_kuc(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    #[must_use = /* ... */]
    pub const fn set_iec(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
}

impl regent::Bitwise for StatusRegister {
    const FIELD_WIDTH: usize = 32;
    type Repr = u32;
    type FromReprFallible = /* private */;

    fn from_repr(repr: Self::Repr) -> Self::FromReprFallible {/* ... */}
    fn to_repr(&self) -> Self::Repr {/* ... */}
    fn into_repr(self) -> Self::Repr {/* ... */}
}

impl regent::BitwiseExt for StatusRegister {
    const REPR_WIDTH: usize = 32;
}
```

</details>

Imagine writing that by hand!

What Regent has done is collapse the struct into a wrapper around a single unsigned integer type, called the *representation* type, and generate a constructor function `new` as well as a getter and setter method for each field. Regent has also implemented the `Bitwise` and `BitwiseExt` traits for the struct; these facilitate conversions to and from the representation and are documented in [the crate documentation][docs].

You may have noticed the `impl regent::Fallible` return types in the `new` function and setter methods. The `Fallible` trait represents an operation that may fail. Crucially, `Fallible` is not the result of the operation, but the operation itself. As such, `Fallible` is inert until explicitly executed via a method that selects the error-handling strategy. The non-immediate execution of functions returning `impl regent::Fallible` is similar to that of `async` functions; in this way, executing a `Fallible` is analogous to polling a `Future` (though `Fallible` is otherwise unrelated to asynchronous programming).

</details>

## Getting Started

If you're ready to use Regent, add [the *regent* crate][crate] to your `Cargo.toml`:

```toml
[dependencies]
regent = "0.2"
```

Then, head over to [the crate documentation][docs] for a semi-formal specification on the `#[bitwise]` macro and information on the runtime `Bitwise` trait.

Otherwise, keep reading for a primer on Rust, bitfields, and Regent.

## Motivation

### What is Rust?

Rust is a new systems programming language with an emphasis on performance and correctness. Rust is primarily imperative with functional influences such as closures, traits, and iterators. Rust also has rich meta-programming capabilities, offering two flavors of macros: declarative macros, which are built into the language, and procedural macros, which are standalone Rust libraries that manipulate the AST directly.

### What are Bitfields?

For all of the things Rust has, *bitfields* it has not. Roughly speaking, a bitfield is an unaligned struct field that inhabits a subset of the bits allowed by its type. These properties allow structs of bitfields to constitute bit patterns that normal structs cannot, like the contents of CPU registers and network packets. Without bitfields, such structures are usually represented by integers and manipulated through handcrafted bitwise operations, which are easy to get wrong and difficult to debug.

<details>
<summary>Motivating Example</summary>
<br>

![Diagram of fields in a CPU register](./resources/mips-r3000-sr.png)

Imagine modeling this structure in your favorite programming language without using bitfields. In C, the *IM* register field might become this:

```c
// Extracts the IM field from the status register.
unsigned SrGetIm(const unsigned sr) {
    return (sr >> 8) & ((1 << 8) - 1);
}

// Sets the IM field in the status register to the given value.
void SrSetIm(unsigned *sr, const unsigned im) {
    const unsigned mask = (1 << 8) - 1;
    // Clear the previous value.
    *sr &= ~(mask << 8);
    // Write the new value.
    *sr |= (im & mask) << 8;
}
```

There is a lot of repetition here. The expression <code>(1&nbsp;<<&nbsp;<em>width</em>)&nbsp;-&nbsp;1</code> keeps showing up, as does the *`offset`* in <code>sr&nbsp;>>&nbsp;<em>offset</em></code>, <code>mask&nbsp;<<&nbsp;<em>offset</em></code>, and <code>(<em>field</em>&nbsp;&&nbsp;mask)&nbsp;<<&nbsp;<em>offset</em></code>. We can introduce some constants and a helper function:

```c
static const unsigned IM_WIDTH = 8;
static const unsigned IM_OFFSET = 8;

static unsigned Mask(const unsigned width) {
    // Note: this is UB when `width` is greater than or equal to the bit-width
    // of the `int` type.
    return (1 << width) - 1;
}

unsigned SrGetIm(const unsigned sr) {
    return (sr >> IM_OFFSET) & Mask(IM_WIDTH);
}

void SrSetIm(unsigned *sr, const unsigned im) {
    const unsigned mask = Mask(IM_WIDTH);
    *sr &= ~(mask << IM_OFFSET);
    *sr |= (im & mask) << IM_OFFSET;
}
```

And now that the getter and setter functions are generic, you might even introduce a macro:

```c
static unsigned Mask(const unsigned width) {
    return (1 << width) - 1;
}

#define FIELD(NAME, WIDTH, OFFSET) \
    unsigned SrGet ## #NAME(const unsigned sr) { \
        return (sr >> OFFSET) & Mask(WIDTH); \
    } \
    void SrSet ## #NAME(unsigned *sr, const unsigned value) { \
        const unsigned mask = Mask(WIDTH); \
        *sr &= ~(mask << OFFSET); \
        *sr |= (value & mask) << OFFSET; \
    }

// It is now trivial to implement the remaining register fields.
FIELD(Iec, 1, 0)
FIELD(Kuc, 1, 1)
FIELD(Iep, 1, 2)
FIELD(Kup, 1, 3)
FIELD(Ieo, 1, 4)
FIELD(Kuo, 1, 5)
FIELD(Im, 8, 8)
FIELD(Isc, 1, 16)
FIELD(Swc, 1, 17)
FIELD(Pz, 1, 18)
FIELD(Cm, 1, 19)
FIELD(Pe, 1, 20)
FIELD(Ts, 1, 21)
FIELD(Bev, 1, 22)
FIELD(Re, 1, 25)
FIELD(Cu0, 1, 28)
FIELD(Cu1, 1, 29)
FIELD(Cu2, 1, 30)
FIELD(Cu3, 1, 31)
```

We are quickly approaching a *declarative* solution.

Now, imagine modeling the same structure with bitfields. Here's what it could look like:

```c
struct Sr {
    bool cu3: 1;
    bool cu2: 1;
    bool cu1: 1;
    bool cu0: 1;
    unsigned _26: 2;
    bool re: 1;
    unsigned _23: 2;
    bool bev: 1;
    bool ts: 1;
    bool pe: 1;
    bool cm: 1;
    bool pz: 1;
    bool swc: 1;
    bool isc: 1;
    unsigned im: 8;
    unsigned _6: 2;
    bool kuo: 1;
    bool ieo: 1;
    bool kup: 1;
    bool iep: 1;
    bool kuc: 1;
    bool iec: 1;
};
```

</details>

### Bitfields in C

Bitfields as a language feature were in part popularized by their inclusion in the [Standard C programming language]. In C, bitfields are formed by a type, identifier, and width:

[Standard C programming language]: https://en.wikipedia.org/wiki/ANSI_C

```c
struct frobnicator {
    unsigned foo: 8;
    unsigned bar: 5;
    unsigned baz: 11;
    _Bool qux_0: 1;
    unsigned qux_1: 4;
    unsigned quux_0: 1;
    unsigned quux_1: 1;
    unsigned quux_2: 1;
};
```

This syntax is *friendly*:

- It is very similar to that of regular struct fields, with the only difference being the <code>:&nbsp;<em>width</em></code> suffix. This syntactical similarity complements the conceptual similarity between bitfields and regular struct fields, and as a practical matter, it flattens the learning curve of the new syntax.
- It plays into the programmer's intuitions. "Hidden information" such as the position and order of bitfields is *encoded* in the position and order of the bitfield declarations themselves.

And you would be forgiven for assuming a good syntax begets good semantics. Unfortunately, many important properties of C bitfields are implementation-defined, undefined, or unspecified, rendering them non-portable at best and dangerous at worst. To name a few:

- The claim that bitfields are ordered according to their declarations is only partly true. C structs are divided into one or more *allocation units*, and the order of bitfields inside an allocation unit is implementation-defined. If, and only if, this order is in the same direction as that of the units themselves, will the order of bitfields correspond to the order of bitfield declarations.
- It is implementation-defined as to whether bitfields may straddle (cross) unit boundaries. If not, padding will be inserted, making the struct no longer tightly-packed.
- The alignment of allocation units is unspecified. This is important if bitfields can straddle unit boundaries, in which case it determines how much padding is inserted.
- It is impossible to specify the backing storage, or internal representation, of a struct comprised of bitfields, nor is there any way to guarantee at compile-time that such a struct is of a particular width or size.
- The allowed types of a bitfield are implementation-defined *with the exception of* `int`, `signed int`, `unsigned int`, and `_Bool`, which are always allowed. Notably, arrays of these types are not explicitly allowed.

These deficiencies have made C bitfields a common source of frustration for programmers and have garnered the bitfield itself a poor reputation.

### Why Regent?

Rust avoided codifying such a controversial feature into the language, leaving the implementation to third-party libraries called *crates*. Regent is one of these crates, and its mission is to combine the intuitive syntax of C bitfields with sane, well-documented semantics.

## Quick Reference

The `#[bitwise]` attribute is a procedural (proc) macro that transforms a non-[ZST] struct item into a [newtype] of an unsigned integer primitive (like `u8` or `u32`) and emits associated functions for accessing struct fields as contiguous ranges of bits within the unsigned integer representation.

`#[bitwise]` struct fields are inhabited by a subset of Rust types, namely: *unsigned integral types*, including the unsigned integer primitives, `bool`, and other `#[bitwise]` structs; tuples of unsigned integral types (e.g., `(u32, bool)`); and arrays of unsigned integral types (e.g., `[u8; 5]`).

In the unsigned integer representation, `#[bitwise]` struct fields are tightly packed (i.e., no padding due to alignment). This applies to the fields themselves as well as the individual elements of tuple or array fields. Consequently, fields are unaligned and arbitrarily wide: a field of type `(u32, bool)` is *exactly* 33 bits wide, and `[u8; 5]` is *exactly* 40 bits.

In theory, you can construct N-bit unsigned integer fields with `[bool; N]`, but `#[bitwise]` offers *pseudo-types* as a simpler alternative. The pseudo-types comprise all types of the form <code>u&#8239;<em>width</em></code> where 1&le;*width*&le;128, including the Rust primitives `u8`, `u16`, `u32`, `u64`, and `u128` in addition to imaginary types like `u5`, `u24`, and `u93`.

The unsigned integral types can also be extended by applying `#[bitwise]` to [unit-only] enum items (i.e., C-style enums).

[ZST]: https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts
[unit-only]: https://doc.rust-lang.org/reference/items/enumerations.html#unit-only-enum
[newtype]: https://doc.rust-lang.org/rust-by-example/generics/new_types.html

## Prior Art

Regent is very similar to these other crates. Please check them out!

- [bilge](https://crates.io/crates/bilge)
- [bitbybit](https://crates.io/crates/bitbybit)
- [modular-bitfield](https://crates.io/crates/modular-bitfield)

## Issues

Bug reports, feature requests, and other enhancements are greatly appreciated!

[crate]: https://crates.io/crates/regent
[docs]: https://docs.rs/regent/latest/regent
[r3000-ref]: https://cgi.cse.unsw.edu.au/~cs3231/doc/R3000.pdf
[r3000-sr]: ./resources/mips-r3000-sr.png
