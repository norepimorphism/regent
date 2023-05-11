fn main() {
    // One variant with one tuple field.
    #[regent::bitwise]
    enum A { _0(u32) }
    // One variant with two tuple fields.
    #[regent::bitwise]
    enum B { _0(u32, u32) }
    // One variant with one struct field.
    #[regent::bitwise]
    enum C { _0 { a: u32 } }
    // One variant with two struct fields.
    #[regent::bitwise]
    enum D { _0 { a: u32, b: u32 } }
    // One variant with fields, one field-less variant.
    #[regent::bitwise]
    enum E { _0(u32), _1 }
    // One field-less variant, one variant with fields.
    #[regent::bitwise]
    enum F { _0, _1(u32) }
    // Two variants, both with fields.
    #[regent::bitwise]
    enum G { _0(u32), _1(u32) }
}
