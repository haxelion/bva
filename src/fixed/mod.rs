mod generics;

pub type BV8 = generics::BV<u8, 1>;
pub type BV16 = generics::BV<u16, 1>;
pub type BV32 = generics::BV<u32, 1>;
pub type BV64 = generics::BV<u64, 1>;
pub type BV128 = generics::BV<u64, 2>;
pub type BV192 = generics::BV<u64, 3>;
pub type BV256 = generics::BV<u64, 4>;
pub type BV320 = generics::BV<u64, 5>;
pub type BV384 = generics::BV<u64, 6>;
pub type BV448 = generics::BV<u64, 7>;
pub type BV512 = generics::BV<u64, 8>;