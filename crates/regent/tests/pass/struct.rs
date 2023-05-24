fn main() {
    #[regent::bitwise(width = 19)]
    pub struct Frobnicator {
        pub foo: u8,
        //pub bar: u5,
        #[constant = 1234]
        pub baz: u11,
        //pub qux: (bool, u4),
        //pub quux: [u1; 3],
    }
}
