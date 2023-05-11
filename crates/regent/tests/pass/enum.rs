fn main() {
    #[regent::bitwise(width = 5)]
    enum A {
        _0,
        _1 = 5,
        _2 = 6,
        _3,
        _4 = 20,
        _5,
    }
}
