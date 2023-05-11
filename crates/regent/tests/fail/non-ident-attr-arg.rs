fn main() {
    // Path (leading colon).
    #[regent::bitwise(::foo = 0)]
    struct A;
    // Path (2 segments).
    #[regent::bitwise(foo::bar = 0)]
    struct B;
    // Path (3 segments).
    #[regent::bitwise(foo::bar::qux = 0)]
    struct C;
}
