# ![Regent. Bitfields in Rust.](resources/logo-subtitle@0.5x.png)

[![crates.io](https://img.shields.io/crates/v/regent)](https://crates.io/crates/regent)
[![docs](https://docs.rs/regent/badge.svg)](https://docs.rs/regent)
[![MPL 2.0 licensed](https://img.shields.io/github/license/norepimorphism/regent)](./LICENSE)

*Regent* is a Rust crate for making bitfield structures. The sole API is the attribute macro `bitwise`, which generates a struct of tightly packed, arbitrarily wide fields with accompanying constructors and accessor methods.

To get started, add the *regent* crate from [crates.io](https://crates.io) to your *Cargo.toml*:

```toml
[dependencies]
regent = "0.2"
```

Then, head over to [docs.rs] to learn how to use *Regent*.

[docs.rs]: https://docs.rs/regent/latest/regent

## Example

<details>
<summary>A code sample demonstrating Regent.</summary>
<br>

The struct definition

```rust
/// A frobnicator.
#[regent::bitwise(width = 32)]
pub struct Frobnicator {
    /// Foo.
    #[constant = 500]
    pub foo: u10,
    /// Bar.
    pub bar: u8,
    /// Baz.
    pub baz: (bool, u4),
    /// Qux.
    pub qux: [u3; 3],
}
```

roughly expands to the following. (Function bodies are omitted for brevity.)

```rust
/// A frobnicator.
#[repr(transparent)]
pub struct Frobnicator(u32);

impl Frobnicator {
    /// Constructs a new `Frobnicator` field-by-field.
    pub fn new(foo: u16, bar: u8, baz: (bool, u8), qux: [u8; 3]) -> Self {/* ... */}

    /// Foo.
    pub const fn foo() -> u16 { 500 }
    /// Bar.
    pub fn bar(&self) -> u8 {/* ... */}
    /// Baz.
    pub fn baz(&self) -> (bool, u8) {/* ... */}
    /// Qux.
    pub fn qux(&self) -> [u8; 3] {/* ... */}

    /// Assigns a new value to the [`bar`] field.
    ///
    /// [`bar`]: Self::bar
    pub fn set_bar(&mut self, field: u8) {/* ... */}
    /// Assigns a new value to the [`baz`] field.
    ///
    /// [`baz`]: Self::baz
    pub fn set_baz(&mut self, field: (bool, u8)) {/* ... */}
    /// Assigns a new value to the [`qux`] field.
    ///
    /// [`qux`]: Self::qux
    pub fn set_qux(&mut self, field: [u8; 3]) {/* ... */}
}

impl regent::Bitwise for Frobnicator {
    const WIDTH: usize = 32;
    type Repr = u32;

    unsafe fn from_repr_unchecked(repr: Self::Repr) -> Self {/* ... */}
    fn from_repr_checked(repr: Self::Repr) -> Option<Self> {/* ... */}
    fn to_repr(&self) -> Self::Repr {/* ... */}
}

impl regent::BitwiseExt for Frobnicator {
    const REPR_WIDTH: usize = 32;
}
```

</details>

## Motivation

### What is Rust?

Rust is a new systems programming language with an emphasis on performance and correctness. Rust is primarily imperative with functional influences such as closures, traits, and iterators. Rust also has rich meta-programming capabilities, offering two flavors of macros: declarative macros, which are built into the language, and procedural macros, which are standalone Rust libraries that manipulate the AST directly.

### What are Bitfields?

For all of the things Rust has, *bitfields* it has not. Roughly speaking, a bitfield is a struct field whose width is measured in bits rather than bytes. Structs comprised of bitfields are tightly-packed, making them convenient for representing dense structures like CPU registers and network packets. Without bitfields, these structures are usually typed as integers and manipulated through hand-crafted bitwise operations. This is a tedious and error-prone process.

Bitfields as a language construct were in part popularized by their inclusion in the C programming language. This offloads the responsibility of bitfield access from the programmer to the compiler, a relatively battle-tested codebase by nature. Unfortunately, the C standard does not give a full treatment of bitfields, and their troubled specification has stifled further language adoption of the bitfield.

Rust avoided codifying such a controversial feature into the language, leaving the implementation to third-party libraries called *crates*. Regent is one of these crates, and its mission is to generate structs comprised of bitfields while inflicting the least amount of pain upon the programmer. The next section, [Prior Art](#prior-art), reviews Regent's influences from C bitfields to the state of Rust bitfield crates today.

## Prior Art

<details>
<summary>A review of existing bitfield implementations.</summary>
<br>

### Bitfields in C

C bitfields are formed by a type, identifier, and width:

```c
struct frobnicator {
    unsigned foo: 10;
    unsigned bar: 8;
    _Bool baz_0: 1;
    unsigned baz_1: 4;
    unsigned qux_0: 3;
    unsigned qux_1: 3;
    unsigned qux_2: 3;
};
```

This syntax is *friendly*:

- It is very similar to that of regular struct fields, with the only difference being the <code>:&nbsp;<em>width</em></code> suffix. This syntactical similarity complements the conceptual similarity between bitfields and regular struct fields, and as a practical matter, it flattens the learning curve of the new syntax.
- It plays into the programmer's intuitions. "Hidden information" such as the position and order of bitfields is *encoded* in the position and order of the bitfield declarations themselves.

And you would be forgiven for assuming a good syntax begets a good feature. Unfortunately, many important properties of C bitfields are implementation-defined, undefined, or unspecified, rendering them non-portable at best and dangerous at worst. To name a few:

- The claim that bitfields are ordered according to their declarations is only partly true. C structs are divided into one or more *allocation units*, and the order of bitfields inside an allocation unit is implementation-defined. If, and only if, this order is in the same direction as that of the units themselves, will the order of bitfields correspond to the order of bitfield declarations.
- It is implementation-defined as to whether bitfields may straddle (cross) unit boundaries. If not, padding will be inserted, making the struct no longer tightly-packed.
- The alignment of allocation units is unspecified. This is important if bitfields can straddle unit boundaries, in which case it determines how much padding is inserted.
- It is impossible to specify the backing storage, or internal representation, of a struct comprised of bitfields, nor is there any way to guarantee at compile-time that such a struct is of a particular width or size.
- The allowed types of a bitfield are implementation-defined *with the exception of* `int`, `signed int`, `unsigned int`, and `_Bool`, which are always allowed. Notably, arrays of these types are not explicitly allowed.

</details>

## Issues

Bug reports, feature requests, and other enhancements are greatly appreciated. Thanks for supporting the project!
