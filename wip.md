# WIP README Sections

## Prior Art

### The *bitfield* Crate

[*bitfield*](https://crates.io/crates/bitfield) by Loïc Damien ([@dzamlo](https://github.com/dzamlo)) was one of the first crates to port bitfields to Rust and originally bore a strong resemblance to C bitfield syntax. It provides the function-like macro `bitfield`.

```rust
bitfield! {
    pub struct Frobnicator(MSB0 u32);
    pub foo, _: 9, 0;
    pub bar, set_bar: 17, 10;
    pub bool, baz_0, set_baz_0: 18;
    pub baz_1, set_baz_1: 22, 19;
    pub qux_0, set_qux_0: 25, 23;
    pub qux_1, set_qux_1: 28, 26;
    pub qux_2, set_qux_2: 31, 29;
}
```

On the one hand, this syntax avoids the ambiguities of C bitfields. The `MSB0` annotation fixes bit 0 as most-significant, which establishes a well-defined order, and the `u32` annotation grounds the struct to a stable internal representation and allows the compiler to guarantee that the sum of bitfield widths does not exceed the width of this representation.

On the other hand, this syntax is neither familiar nor intuitive. It can be inferred that the <code>3,&nbsp;0</code> and friends on the right-hand side correspond to the range of bits each bitfield inhabits. However, this displaces type annotations, and these ranges do not resemble the standard Rust range syntax `start..=end`. Furthermore, the bitfield declarations being at the same level as the struct declaration is counter-intuitive to the logical ownership of fields by a struct, which Rust expresses by nesting the fields within a block.

In some ways, this `bitfield` macro is more powerful than C bitfields. Most notably, defining a bitfield by its range rather than width allows bitfields to overlap. In overlapping cases, this might be a reasonable syntax. However, I contend that in all non-overlapping cases, this syntax is more verbose and more error-prone than that of C. For example, it is easy to make an off-by-one error when specifying the range of a bitfield and inadvertently overlap adjacent bitfields by one bit:

```rust
    // ...
    pub version, set_version:            3,  0;
    pub ihl, set_ihl:                    7,  3;
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ^ This is wrong!
    pub dscp, set_dscp:                 13,  8;
    // ...
```

### The *modular-bitfield* Crate

The crate [*modular-bitfield*](https://crates.io/crates/modular-bitfield) is developed by Robin Freyler ([@Robbepop](https://github.com/Robbepop)) and inspired by David Tolnay's ([@dtolnay](https://github.com/dtolnay)) [proc macro workshop](https://github.com/dtolnay/proc-macro-workshop/blob/master/README.md). Its core API is the `bitfield` attribute macro. Let's apply the `ipv4_header_0` test:

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

## Specification

### Field Types

The bit width of a field is inferred by the type, which can be `bool`; an arbitrary-width unsigned integer of the form <code>u&#8239;<em>width</em></code>; an implementor of the `regent::Bitwise` trait, such as a type annotated with the `bitwise` attribute; or a tuple or array of the these types.

Fields, as well as tuple and array elements, are tightly packed and are not aligned in any way.

| Type                                  | Width (bits)                       |
|---------------------------------------|------------------------------------|
| `bool`                                | 1                                  |
| <code>u&#8239;<em>width</em></code>   | *width*                            |
| `(A, B, ...)`                         | sum of widths of `A`, `B`, ...     |
| <code>[T;&nbsp;<em>*len*</em>]</code> | product of *len* and width of `T`  |

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

- Zero-sized types, including the 0-width integer `u0`, the unit `()`, and the 0-element array <code>[_;&nbsp;0]</code>, are disallowed. A struct annotated with `bitwise` cannot be zero-sized, nor can the type of any single field within a struct be zero-sized.
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
