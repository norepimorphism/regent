fn main() {
    // Duplicate path, duplicate value (2).
    #[regent::bitwise(size = 1, size = 1)]
    struct A;
    // Duplicate path, unique values (2).
    #[regent::bitwise(size = 1, size = 2)]
    struct B;
    // Duplicate path, duplicate value (3).
    #[regent::bitwise(size = 1, size = 1, size = 1)]
    struct C;
    // Duplicate path, unique values (3).
    #[regent::bitwise(size = 1, size = 2, size = 3)]
    struct D;
}
