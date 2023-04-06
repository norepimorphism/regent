# ![Regent](resources/regent@0.5x.png)

Bitfields in Rust.

Regent provides the attribute macro `bitwise` which generates methods for accessing struct fields of arbitrary bit widths.

## Usage

Add the *regent* crate from [crates.io](https://crates.io) to your *Cargo.toml*:

```toml
[dependencies]
regent = "0.1"
```

## Examples

This struct:

```rust
#[regent::bitwise]
struct Timestamp {
    // 1900..=2411
    year: u9,
    // 1..=16
    month: u4,
    // 1..=32
    day: u5,
}
```

...roughly expands to:

```rust
#[repr(transparent)]
struct Timestamp(u32);

// (Function bodies are omitted for brevity.)

impl Timestamp {
    fn new(year: u16, month: u8, day: u8) -> Self {/* ... */}

    fn year(&self) -> u16 {/* ... */}
    fn month(&self) -> u8 {/* ... */}
    fn day(&self) -> u8 {/* ... */}

    fn set_year(&mut self, field: u16) {/* ... */}
    fn set_month(&mut self, field: u8) {/* ... */}
    fn set_day(&mut self, field: u8) {/* ... */}
}

impl regent::Bitwise for Timestamp {
    const WIDTH: usize = 18;
    type Repr = u32;

    unsafe fn from_repr_unchecked(repr: Self::Repr) -> Self {/* ... */}
    fn from_repr_checked(repr: Self::Repr) -> Option<Self> {/* ... */}
    fn to_repr(&self) -> Self::Repr {/* ... */}
}

impl regent::BitwiseExt for Timestamp {
    const REPR_WIDTH: usize = 32;
}
```

To serialize a `Timestamp` into a `u32`, you might write:

```rust
use regent::Bitwise as _;

let se = Timestamp::new(year, month, day).to_repr();
```

To deserialize a `Timestamp` from a `u32`, you might write:

```rust
let de = Timestamp::from_repr(se);
let (year, month, day) = (de.year(), de.month(), de.day());
```

## Design

### Field Types

The bit width of a field is inferred by the type, which can be `bool`; an arbitrary-width unsigned integer of the form `u`*width*; an implementor of the `regent::Bitwise` trait, such as a type annotated with the `bitwise` attribute; or a tuple or array of the these types.

Fields, as well as tuple and array elements, are tightly packed and are not aligned in any way.

| Type           | Width (bits)                       |
|----------------|------------------------------------|
| `bool`         | 1                                  |
| `u`*width*     | *width*                            |
| `(A, ...)`     | sum of widths of constituent types |
| `[T;` *len*`]` | product of *len* and width of `T`  |

### Internal Representation

`bitwise` structs are transparently represented by an unsigned integer of the minimum available width large enough to contain all fields. Because Rust offers a limited set of unsigned integer primitives, a struct in which the total width of its fields does not correspond to an existing primitive is 'rounded up' to the next-smallest representation.

Take the `Timestamp` struct from the [Examples](#examples) section:

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

- Zero-sized types, including the 0-width integer `u0`, the unit `()`, and the 0-element array `[_; 0]`, are disallowed. A struct annotated with `bitwise` cannot be zero-sized, nor can the type of any single field within a struct be zero-sized.
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

## Issues

Bug reports, feature requests, and other enhancements are greatly appreciated. Kindly submit them to the GitHub repository.

## Acknowledgements

Regent was originally developed as part of the PlayStation emulator [Noctane](https://github.com/norepimorphism/noctane) to model CPU and MMIO registers, but it has since been factored out into its own GitHub repository.

### modular-bitfield

Regent is inspired by the [*modular-bitfield*](https://crates.io/crates/modular-bitfield) crate, created by Robin Freyler ([@Robbepop](https://github.com/Robbepop)) and itself inspired by David Tolnay's ([@dtolnay](https://github.com/dtolnay)) [proc macro workshop](https://github.com/dtolnay/proc-macro-workshop/blob/master/README.md). (Go check it out!)

In particular, I liked the ergonomics of field access via `Struct::field` and `Struct::set_field` methods but found the `Struct::new` and `Struct::with_field` mechanism made it too easy to accidentally leave fields uninitialized, and I did not like how many items are brought into scope with `use modular_bitfield::prelude::*`, which defines analogue types to Regent's `u`*width* pseudo-types (among other things). *modular-bitfield* is a superb crate overall, but I wanted something a little different for Noctane.
