fn main() {
    // Array.
    #[regent::bitwise]
    enum A { _0 = [0] }
    // Boolean.
    #[regent::bitwise]
    enum B { _0 = true }
    // Character.
    #[regent::bitwise]
    enum C { _0 = 'a' }
    // String.
    #[regent::bitwise]
    enum D { _0 = "abc" }
    // Tuple.
    #[regent::bitwise]
    enum E { _0 = () }
}
