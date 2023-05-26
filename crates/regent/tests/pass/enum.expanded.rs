fn main() {
    #[repr(u8)]
    enum A {
        _0,
        _1 = 5,
        _2 = 6,
        _3,
        _4 = 20,
        _5,
    }
    impl ::regent::Bitwise for A {
        const WIDTH: usize = 5;
        type Repr = u8;
        unsafe fn from_repr_unchecked(repr: Self::Repr) -> Self {
            ::core::mem::transmute(repr)
        }
        fn from_repr_checked(repr: Self::Repr) -> ::core::option::Option<Self> {
            match repr {
                0 => ::core::option::Option::Some(Self::_0),
                5 => ::core::option::Option::Some(Self::_1),
                6 => ::core::option::Option::Some(Self::_2),
                7 => ::core::option::Option::Some(Self::_3),
                20 => ::core::option::Option::Some(Self::_4),
                21 => ::core::option::Option::Some(Self::_5),
                _ => ::core::option::Option::None,
            }
        }
        fn to_repr(&self) -> Self::Repr {
            unsafe { ::core::ptr::read(self as *const Self as *const _) }
        }
        fn into_repr(self) -> Self::Repr {
            self as _
        }
    }
}
