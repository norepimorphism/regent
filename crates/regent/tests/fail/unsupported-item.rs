fn main() {
    // Module.
    #[regent::bitwise]
    mod module {}
    // `use` declaration.
    #[regent::bitwise]
    use module::*;
    // Function definition.
    #[regent::bitwise]
    fn function() {}
    // Type definition.
    #[regent::bitwise]
    type Type = ();
    // Union definition.
    #[regent::bitwise]
    union Union {}
    // Constant item.
    #[regent::bitwise]
    const CONST: () = ();
    // Static item.
    #[regent::bitwise]
    static STATIC: () = ();
    // Trait definition.
    #[regent::bitwise]
    trait Trait {}
    // Implementation.
    #[regent::bitwise]
    impl Trait for Union {}
    // Extern block.
    #[regent::bitwise]
    extern "C" {}
}
