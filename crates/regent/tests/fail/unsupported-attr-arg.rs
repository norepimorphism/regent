fn main() {
    // Unsupported.
    #[regent::bitwise(foo = 0)]
    struct A;
    // Supported, unsupported.
    #[regent::bitwise(size = 1, foo = 0)]
    struct B;
    // Unsupported, supported.
    #[regent::bitwise(foo = 0, size = 1)]
    struct C;
    // Unsupported, unsupported.
    #[regent::bitwise(foo = 0, bar = 0)]
    struct D;
}
