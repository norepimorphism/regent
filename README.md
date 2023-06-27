# ![Regent. Bitfields in Rust.](resources/logo-subtitle@0.5x.png)

[![crates.io](https://img.shields.io/crates/v/regent)][crate]
[![docs.rs](https://docs.rs/regent/badge.svg)][docs]
[![MPL-2.0 license](https://img.shields.io/github/license/norepimorphism/regent)](./LICENSE)

> **⚠️ NOTICE: This README is Under Construction**
>
> This README is incomplete and describes a version of Regent which is not yet available on crates.io.

*Regent* is an ecosystem of [Rust] crates for making bitfield structures. The sole API is the attribute macro `#[bitwise]`, which generates a struct of tightly packed, arbitrarily wide fields with accompanying constructors and accessor methods.

[Rust]: https://www.rust-lang.org/

## Features

- `#![no_std]`
- Associated functions are `const fn` wherever possible
- No [leaky abstractions]&mdash;`#[bitwise]` does not pollute the call-site scope with items that expose implementation details (like `mod __private`)
- Minimum supported Rust version (MSRV) is [1.67.0]

[leaky abstractions]: https://en.wikipedia.org/wiki/Leaky_abstraction
[1.67.0]: https://blog.rust-lang.org/2023/01/26/Rust-1.67.0.html

## Guided Example

<details>
<summary>
    <strong>The fastest way to learn Regent is by example.</strong> This section demonstrates a typical use case for Regent, introducing features gradually to approach a succinct and idiomatic solution. Familiarity with Rust is assumed.
</summary>
<br>

The MIPS R3000 is a 32-bit RISC microprocessor. Like many CPUs, the R3000 has a status register (SR) that holds system variables pertaining to the architecture. Here's a diagram of it:

![Diagram of the fields in a 32-bit CPU register.](./resources/mips-r3000-sr.png)

> Source: [*IDT R30xx Family Software Reference Manual*][r3000-ref], published in 1994 by Integrated Device Technology, Inc.

[r3000-ref]: https://cgi.cse.unsw.edu.au/~cs3231/doc/R3000.pdf

Each system variable corresponds to a register *field*, depicted here as a rectangle. Most fields are labeled, but a few enclose the text "0"; these fields are immutable and always read zero. Above each field are the positions of its most- and least-significant bits (or just the position of the field if it is 1-bit). The bit in position 0 is the least-significant bit of the register, and bit 31 is the most significant.

### A First Attempt

We can model the SR with the `#[bitwise]` macro from Regent:

```rust
#[regent::bitwise(width = 32)]
pub struct StatusRegister {
    pub cu3: bool,
    pub cu2: bool,
    pub cu1: bool,
    pub cu0: bool,
    #[const]
    _26: u2,
    pub re: bool,
    #[const]
    _23: u2,
    pub bev: bool,
    pub ts: bool,
    pub pe: bool,
    pub cm: bool,
    pub pz: bool,
    pub swc: bool,
    pub isc: bool,
    pub im: u8,
    #[const]
    _6: u2,
    pub kuo: bool,
    pub ieo: bool,
    pub kup: bool,
    pub iep: bool,
    pub kuc: bool,
    pub iec: bool,
}
```

`#[bitwise]` parses a struct-like syntax. It largely overlaps with Rust's [struct item syntax] but has different semantics&mdash;most importantly, `#[bitwise]` fields are bit-packed rather than aligned at byte boundaries. `#[bitwise]` also supports several new constructs, some of which appear here in `StatusRegister`. These are:

[struct item syntax]: https://doc.rust-lang.org/reference/items/structs.html

- **The `width = 32` argument to the `#[bitwise]` attribute.** This informs Regent that the widths of all struct fields should sum to 32 bits. If they do not, Regent will emit a compile-time error.
  - You can write `size = 4` instead if you prefer to specify the width in bytes.
  - It is good practice&mdash;and is, in some cases, required&mdash;to include either a `width` or `size` argument. These help catch simple mistakes like missing or duplicated fields and serve as visual reminders of the struct width.
  - The value passed to `width` or `size` must be an unsuffixed, unsigned integer literal.
- **The `#[const]` attribute.** This imbues a struct field with a compile-time constant value of `Default::default()`. Fields annotated with `#[const]` are called *constant fields*.
  - You can assign a custom constant value like `#[const = 0]`. Constant values can be any [constant expression] that is valid for the type of the field.
- **The `u2` type**. This is an imaginary 2-bit unsigned integer type. Regent provides built-in `u*` types for all unsigned integers 1 to 128 bits wide (but not `usize`).

[constant expression]: https://doc.rust-lang.org/reference/const_eval.html#constant-expressions

At macro evaluation time, `#[bitwise]` expands the struct to (roughly) the following. (Function bodies are omitted for brevity.)

<details>
<summary>Expanded code</summary>
<br>

```rust
#[repr(transparent)]
pub struct StatusRegister(regent::Opaque<u32>);

impl StatusRegister {
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

    // Getters
    pub const fn cu3(&self) -> bool {/* ... */}
    pub const fn cu2(&self) -> bool {/* ... */}
    pub const fn cu1(&self) -> bool {/* ... */}
    pub const fn cu0(&self) -> bool {/* ... */}
    const fn _26() -> u8 { 0 }
    pub const fn re(&self) -> bool {/* ... */}
    const fn _23() -> u8 { 0 }
    pub const fn bev(&self) -> bool {/* ... */}
    pub const fn ts(&self) -> bool {/* ... */}
    pub const fn pe(&self) -> bool {/* ... */}
    pub const fn cm(&self) -> bool {/* ... */}
    pub const fn pz(&self) -> bool {/* ... */}
    pub const fn swc(&self) -> bool {/* ... */}
    pub const fn isc(&self) -> bool {/* ... */}
    pub const fn im(&self) -> u8 {/* ... */}
    const fn _6() -> u8 { 0 }
    pub const fn kuo(&self) -> bool {/* ... */}
    pub const fn ieo(&self) -> bool {/* ... */}
    pub const fn kup(&self) -> bool {/* ... */}
    pub const fn iep(&self) -> bool {/* ... */}
    pub const fn kuc(&self) -> bool {/* ... */}
    pub const fn iec(&self) -> bool {/* ... */}

    // Setters
    pub const fn set_cu3(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_cu2(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_cu1(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_cu0(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_re(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_bev(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_ts(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_pe(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_cm(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_pz(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_swc(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_isc(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_im(&mut self, field: u8) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_kuo(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_ieo(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_kup(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_iep(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
    pub const fn set_kuc(&mut self, field: bool) -> impl regent::Fallible<Output = ()> {/* ... */}
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

What Regent has done is collapse the struct into a wrapper around a single unsigned integer type called the *representation*&mdash;expressed here by the newtype `regent::Opaque<u32>`&mdash;and generate a constructor function `new` as well as a getter and setter method for each field (except for constant fields, which have only a getter). Regent has also implemented the `Bitwise` and `BitwiseExt` traits for the struct; these facilitate conversions to and from the representation and are documented in [the crate documentation][docs].

### The `Fallible` Trait

Some functions emitted by `#[bitwise]` are fallible, meaning they may encounter errors. The `new` function fails if any argument is not a valid value for the type of its corresponding field. Likewise, setters fail if their argument is invalid for the field being set.

There are numerous strategies for handling and recovering from errors, each with trade-offs, so it is often desirable for an API to support a variety for any given fallible operation. Because some strategies necessitate different function signatures than others, a fallible operation is commonly broken into multiple functions that each implement the operation with a different error-handling strategy.

A common idiom in Rust is for a fallible function `f` to have `checked_f` and `unchecked_f` versions. By convention, `f` takes the form `fn(...) -> T` and panics on error; `checked_f` has signature `fn(...) -> Option<T>` and returns `None` on error; and `unchecked_f` is `unsafe fn(...) -> T` and performs no error-checking at all (possibly causing UB if an error condition arises).

Regent takes an alternative yet functionally equivalent approach[^fallible-trait] in which the error-handling strategies available to a fallible operation are realized as associated functions of a trait. An existential type[^existential-type] (`impl Trait`) implementing the trait is then produced by an associated function of `T` that stands in for the fallible operation.

[^fallible-trait]: The reasons for this approach were originally based on aesthetic preference of the author (rather than something more important, like genericity or ease of implementation). I would be happy to host discussion of this choice and potential arguments for alternatives in a [GitHub discussion].
[^existential-type]: [varkor] gives an excellent introduction to existential types in Rust; see <https://varkor.github.io/blog/2018/07/03/existential-types-in-rust.html>.

[GitHub discussion]: https://github.com/norepimorphism/regent/discussions/new?category=general
[varkor]: https://github.com/varkor

In Regent, the trait is `regent::Fallible`&mdash;roughly defined as

```rust
pub trait Fallible {
    type Output;

    // Panics on the first error.
    fn panicking(self) -> Self::Output;
    // Returns `None` on the first error.
    fn checked(self) -> Option<Self::Output>;
    // Ignores all errors.
    fn masked(self) -> Self::Output;
    // Assumes that errors cannot occur.
    unsafe fn unchecked(self) -> Self::Output;
}
```

&mdash;and the existential type which implements it is `impl Fallible`.
All fallible functions return this type. You can use them like this:

```rust
// Bring `Fallible` into scope.
use regent::Fallible as _;

let _: StatusRegister = StatusRegister::new(/* ... */).panicking();
let _: StatusRegister = StatusRegister::new(/* ... */).masked();
let _: Option<StatusRegister> = StatusRegister::new(/* ... */).checked();
unsafe {
    let _: StatusRegister = StatusRegsiter::new(/* ... */).unchecked();
}
```

The most important thing to remember is: `impl Fallible` is not the result of a fallible operation, but rather the operation itself. As such, it is inert until explicitly executed via a method that selects the error-handling strategy. The non-immediate execution of functions returning `impl Fallible` is similar to that of `async` functions; in this way, executing a `Fallible` is analogous to `.await`ing a `Future` (though `Fallible` is otherwise unrelated to asynchronous programming).

### Fine-Tuning

Our definition of `StatusRegister` is workable, but there is room for improvement.

One such improvement which requires only minor modification involves the constant fields presently named `_26`, `_23`, and `_6`; these correspond to the zero-filled register fields that inhabit bits 26&ndash;27, 23&ndash;24, and 6&ndash;7, respectively. To a MIPS programmer, these are not very useful and are only defined in `StatusRegister` to conform with the MIPS standard. Hence, we will consider them implementation details which should have no effect outside the definition of `StatusRegister`.

We have already taken one step in this direction, that being the omission of a visibility specifier (e.g., `pub`), and this prevents associated functions from being exported to parent modules or external crates. But ideally, we wish to suppress those functions from being emitted in the first place.

In Regent, this can be done by replacing the field identifier with the underscore token `_` as shown below. (This is not possible in vanilla Rust as idents cannot be `_`[^wildcard-ident].)

[^wildcard-ident]: You might object that many grammatical constructs in Rust, like `let` bindings and destructuring patterns, allow `_` to be used like an ident. This is because their syntax accepts a pattern, which can be formed by an ident or `_` (among many other constructions). But in general, an ident cannot be `_`, and this is indeed the case for struct fields.

```rust
#[regent::bitwise(width = 32)]
pub struct StatusRegister {
    pub cu3: bool,
    pub cu2: bool,
    pub cu1: bool,
    pub cu0: bool,
    #[const]
    _: u2,          // NEW
    pub re: bool,
    #[const]
    _: u2,          // NEW
    pub bev: bool,
    pub ts: bool,
    pub pe: bool,
    pub cm: bool,
    pub pz: bool,
    pub swc: bool,
    pub isc: bool,
    pub im: u8,
    #[const]
    _: u2,          // NEW
    pub kuo: bool,
    pub ieo: bool,
    pub kup: bool,
    pub iep: bool,
    pub kuc: bool,
    pub iec: bool,
}
```

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
