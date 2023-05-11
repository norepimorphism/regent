fn main() {
    // Mutually-exclusive paths, same semantics.
    #[regent::bitwise(size = 1, width = 8)]
    struct A;
    // Mutually-exclusive paths, different semantics.
    #[regent::bitwise(size = 1, width = 1)]
    struct B;
}
