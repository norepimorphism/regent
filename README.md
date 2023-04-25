# ![Regent](resources/regent@0.5x.png)

[![crates.io](https://img.shields.io/crates/v/regent)](https://crates.io/crates/regent)
[![docs](https://docs.rs/regent/badge.svg)](https://docs.rs/regent)
[![MPL 2.0 licensed](https://img.shields.io/github/license/norepimorphism/regent)](./LICENSE)

**Bitfields in Rust.**

*Regent* is a Rust crate to help reduce the anguish associated with modeling binary data formats. The core API entrypoint is the attribute macro `bitwise`, which generates a struct of tightly-packed, arbitrary-width fields with accompanying constructors and accessor methods.

To get started, add the *regent* crate from [crates.io](https://crates.io) to your *Cargo.toml*:

```toml
[dependencies]
regent = "0.2"
```

## Example

<details>
<summary>The fastest way to understand how Regent works is by example.</summary>
<br>

This struct definition:

```rust
/// The first 32-bit word of an IPv4 header.
#[regent::bitwise(width = 32)]
pub struct Ipv4Header0 {
    /// The version of the Internet Protocol in use.
    ///
    /// For IPv4 packets, this is always 4.
    #[constant(value = "4")]
    pub version: u4,
    /// The Internet Header Length (IHL).
    pub ihl: u4,
    /// The Differentiated Services Code Point (DSCP).
    pub dscp: u6,
    /// The Explicit Congestion Notification (ECN).
    pub ecn: u2,
    /// The size, in bytes, of the entire packet.
    pub total_length: u16,
}
```

...roughly expands to the following:

```rust
/// The first 32-bit word of an IPv4 header.
#[repr(transparent)]
pub struct Ipv4Header0(u32);

// (Function bodies are omitted for brevity.)

impl Ipv4Header0 {
    /// Constructs a new `Ipv4Header0` field-by-field.
    fn new(ihl: u8, dscp: u8, ecn: u8, total_length: u16) -> Self {/* ... */}

    /// The version of the Internet Protocol in use.
    ///
    /// For IPv4 packets, this is always 4.
    const fn version() -> u8 { 4 }

    /// The Internet Header Length (IHL).
    fn ihl(&self) -> u8 {/* ... */}

    /// The Differentiated Services Code Point (DSCP).
    fn dscp(&self) -> u8 {/* ... */}

    /// The Explicit Congestion Notification (ECN).
    fn ecn(&self) -> u8 {/* ... */}

    /// The size, in bytes, of the entire packet.
    fn total_length(&self) -> u16 {/* ... */}

    /// Assigns a new value to the [`ihl`] field.
    ///
    /// Because `ihl` is a 4-bit field, the most-significant 4 bits of `field` are ignored.
    fn set_ihl(&mut self, field: u8) {/* ... */}

    /// Assigns a new value to the [`dscp`] field.
    ///
    /// Because `dscp` is a 6-bit field, the most-significant 2 bits of `field` are ignored.
    fn set_dscp(&mut self, field: u8) {/* ... */}

    /// Assigns a new value to the [`ecn`] field.
    ///
    /// Because `ecn` is a 2-bit field, the most-significant 6 bits of `field` are ignored.
    fn set_ecn(&mut self, field: u8) {/* ... */}

    /// Assigns a new value to the [`total_length`] field.
    fn set_total_length(&mut self, field: u16) {/* ... */}
}

impl regent::Bitwise for Ipv4Header0 {
    const WIDTH: usize = 32;
    type Repr = u32;

    unsafe fn from_repr_unchecked(repr: Self::Repr) -> Self {/* ... */}
    fn from_repr_checked(repr: Self::Repr) -> Option<Self> {/* ... */}
    fn to_repr(&self) -> Self::Repr {/* ... */}
}

impl regent::BitwiseExt for Ipv4Header0 {
    const REPR_WIDTH: usize = 32;
}
```

</details>

## Motivation

<details>
<summary>A story of Rust, C, and bitfields.</summary>
<br>

### What is Rust?

Rust is a modern systems programming language with an emphasis on performance and correctness. Rust is primarily imperative with functional influences such as closures, traits, and iterators. Rust also has rich meta-programming capabilities, offering two flavors of macros: declarative macros, which are built into the language, and procedural macros, which are standalone Rust libraries that manipulate the AST directly.

### What are Bitfields?

For all of the things Rust has, *bitfields* it has not. Roughly speaking, a bitfield is a struct field whose width is measured in bits rather than bytes. Structs comprised of bitfields are tightly-packed, making them convenient for representing dense structures like CPU registers and network packets.

Bitfields as a data structure were in part popularized by their inclusion in the C programming language. Unfortunately, the C standard has not given a fair treatment of bitfields, and their troubled specification stifles further adoption of the bitfield as a language construct. Rust wisely avoided introducing such a controversial feature into the language, leaving their implementation to third-party libraries called *crates*.

Regent is one such crate, and its mission is to facilitate the generation of structs comprised of bitfields while inflicting the least amount of pain upon the programmer. Let's take a stroll through Regent's influences, beginning with C.

### Bitfields in C

C bitfields are formed by a type, identifier, and width:

```c
struct ipv4_header_0 {
    unsigned version : 4;
    unsigned ihl : 4;
    unsigned dscp : 6;
    unsigned ecn : 2;
    unsigned total_length : 16;
};
```

I think this is a good syntax, for several reasons:

- It is very similar to that of regular struct fields, with the only difference being the `:`&nbsp;`width` suffix. This accents the conceptual similarity between bitfields and regular struct fields, and as a practical matter, it flattens the learning curve of the new syntax.
- It plays into the programmer's intuitions. "Hidden information" such as the position and order of bitfields is encoded in the position and order of the bitfield declarations themselves.

And you would be forgiven for assuming a good syntax begets a good feature. But, many important properties of C bitfields are implementation-defined, undefined, or unspecified, rendering them unportable at best and dangerous at worst.

For example, correspondence between the order of bitfield declarations and the order of the actual bitfields is not necessarily guaranteed. Adjacent bitfield declarations will probably correspond to adjacent bitfields, but whether the first bitfield declaration is most- or least-significant is implementation-defined.

There is similarly no straightforward way to specify the backing storage, or internal representation, of a struct comprised of bitfields, nor is there any way to guarantee at compile-time that such a struct is of a particular width or size.

</details>

## Prior Art

<details>
<summary>A review of existing Rust crates with similar goals.</summary>
<br>

### The *bitfield* Crate

The aptly-named [*bitfield*](https://crates.io/crates/bitfield) by Loïc Damien ([@dzamlo](https://github.com/dzamlo)) provides the function-like macro `bitfield`. The `ipv4_header_0` struct from earlier can be expressed like this:

```rust
bitfield! {
    pub struct Ipv4Header0(MSB0 u32);
    pub version, set_version:            3,  0;
    pub ihl, set_ihl:                    7,  4;
    pub dscp, set_dscp:                 13,  8;
    pub ecn, set_ecn:                   15, 14;
    pub total_length, set_total_length: 31, 16;
}
```

On the one hand, this syntax provides a mechanism for specifying which bitfield is most- or least-significant, avoiding the ordering fiasco of C bitfields. Another improvement upon C is the explicit type annotation of the struct itself, which grounds it to a stable internal representation and allows the compiler to guarantee that the sum of bitfield widths does not exceed the width of this representation.

On the other hand, this syntax is neither familiar nor intuitive. It can be inferred that the `3,`&nbsp;`0` and friends on the right-hand side correspond to the range of bits each bitfield inhabits. However, this displaces field type annotations, and these ranges also run counter-intuitive to the idiomatic Rust range syntax `start..end`. Furthermore, the bitfield declarations being at the same level as the struct declaration defies the logical ownership of fields by a struct, which is idiomatically expressed by nesting the fields within a block.

In some ways, this `bitfield` macro is more powerful than C bitfields. Most notably, defining a bitfield by its range rather than width allows bitfields to overlap. In overlapping cases, this might be a reasonable syntax. However, I contend that in all non-overlapping cases, this syntax is more verbose and more error-prone than that of C. For example, it is easy to make an off-by-one error when specifying the range of a bitfield and inadvertently overlap adjacent bitfields by one bit:

```rust
    // ...
    pub version, set_version:            3,  0;
    pub ihl, set_ihl:                    7,  3;
                                         /* ^^^ This is wrong! */
    pub dscp, set_dscp:                 13,  8;
    // ...
```

### The *modular-bitfield* Crate

[*modular-bitfield*](https://crates.io/crates/modular-bitfield) is developed by Robin Freyler ([@Robbepop](https://github.com/Robbepop)) and inspired by David Tolnay's ([@dtolnay](https://github.com/dtolnay)) [proc macro workshop](https://github.com/dtolnay/proc-macro-workshop/blob/master/README.md). Its core API is the `bitfield` attribute macro. Let's apply the `ipv4_header_0` test:

```rust
use modular_bitfield::prelude::*;

#[bitfield]
pub struct Ipv4Header0 {
    pub version: B4,
    pub ihl: B4,
    pub dscp: B6,
    pub ecn: B2,
    pub total_length: B16,
}
```

*modular-bitfield* does many things right.

For one, `Ipv4Header0` actually *looks* like a proper struct definition, which helps the programmer infer that `B4` and friends are types of varying bit-widths.

TODO

</details>

## Design

<details>
<summary>How Regent works and how to use it.</summary>
<br>

### Field Types

The bit width of a field is inferred by the type, which can be `bool`; an arbitrary-width unsigned integer of the form `u`*width*; an implementor of the `regent::Bitwise` trait, such as a type annotated with the `bitwise` attribute; or a tuple or array of the these types.

Fields, as well as tuple and array elements, are tightly packed and are not aligned in any way.

| Type           | Width (bits)                       |
|----------------|------------------------------------|
| `bool`         | 1                                  |
| `u`*width*     | *width*                            |
| `(A, B, ...)`  | sum of widths of `A`, `B`, ...     |
| `[T;` *len*`]` | product of *len* and width of `T`  |

### Internal Representation

`bitwise` structs are transparently represented by an unsigned integer of the minimum available width large enough to contain all fields. Because Rust offers a limited set of unsigned integer primitives, a struct in which the total width of its fields does not correspond to an existing primitive is 'rounded up' to the next-smallest representation.

Take the `Timestamp` struct:

```rust
#[regent::bitwise]
struct Timestamp {
    year: u9,
    month: u4,
    day: u5,
}
```

A 9-bit year, 4-bit month, and 5-bit day makes an 18-bit timestamp, which is rounded up to a `u32`. Hence, Regent generates this definition:

```rust
#[repr(transparent)]
struct Timestamp(u32);
```

Internally, `Timestamp` is represented in binary as:

```txt
   (unused)     day  month  year
00000000000000 ddddd mmmm yyyyyyyyy
^ bit 31                          ^ bit 0
```

The first field is taken to be 'least-significant', and the last field is 'most-significant'.

### Field Access

This definition of `Timestamp` does not permit field access via dot-notation like `timestamp.year`. Instead, Regent generates the methods `Timestamp::year` and `Timestamp::set_year` to read from and write to the `year` field.

Similarly to how struct representations are 'rounded up' to the next-smallest unsigned integer primitive, the return type of `Timestamp::year` and argument type to `Timestamp::set_year` are 'rounded up' from the imaginary `u9` type to the `u16` primitive. Hence, Regent generates these method signatures:

```rust
impl Timestamp {
    fn year(&self) -> u16 {/* ... */}
    fn set_year(&mut self, field: u16) {/* ... */}
}
```

`Timestamp::year` zero-extends the `year` field, and `Timestamp::set_year` ignores the most-significant 5 bits of `field`.

### Visibility

Regent respects the visibility of items and struct fields. Struct visibility propagates to the `new` method, and per-field visibility affects getter and setter methods. Visibility qualifiers are ignored on constant fields.

### Tuple Structs

Regent has basic support for tuple structs annotated with `bitwise`. This definition:

```rust
#[regent::bitwise]
struct TupleStruct(u7, bool);
```

...roughly expands to:

```rust
#[repr(transparent)]
struct TupleStruct(u8);

impl TupleStruct {
    fn _0(&self) -> u8 {/* .. */}
    fn set_0(&mut self, field: u8) {/* ... */}

    fn _1(&self) -> bool {/* ... */}
    fn set_1(&mut self, field: bool) {/* ... */}
}

// ...
```

### Constant Fields

Struct fields annotated with the `#[constant]` attribute are assigned a constant value in the `new` method. Getters and setters are not generated for these fields.

By default, the value of a constant field is `Default::default()`. This behavior can be overridden by supplying a `value = "..."` argument to the attribute. For example:

```rust
#[regent::bitwise]
struct Complex(
    u8,
    u16,
    #[constant(value = "123456")]
    u32,
    #[constant]
    bool,
);
```

`Complex::new` initializes the `u32` field with `123_456u32`, and the `bool` field is initialized `false`.

### Restrictions

Regent places some restrictions on how the `bitwise` macro may be used. These include:

- Zero-sized types, including the 0-width integer `u0`, the unit `()`, and the 0-element array `[_;`&nbsp;`0]`, are disallowed. A struct annotated with `bitwise` cannot be zero-sized, nor can the type of any single field within a struct be zero-sized.
- Tuples and arrays cannot be nested in a struct field, e.g., you cannot have:

    ```rust
    #[regent::bitwise]
    struct A([(u8, bool); 10]);
    ```

    This may be made a feature in the future.
- Generic parameters are not supported on structs, e.g., you cannot have:

    ```rust
    #[regent::bitwise]
    struct A<T>([T; 5]);
    ```

  This may be made a feature in the future.
- The length of an array (in the context of a struct field) must be an integer literal. Non-trivial constant expressions such as `8 * 4` are not supported for technical reasons.

</details>

## Issues

Bug reports, feature requests, and other enhancements are greatly appreciated. Thanks for supporting Regent!

## Acknowledgements

Regent was originally developed as part of the PlayStation emulator [Noctane](https://github.com/norepimorphism/noctane) to model CPU and MMIO registers, but it has since been factored out into its own GitHub repository.
