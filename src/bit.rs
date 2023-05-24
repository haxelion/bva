use std::convert::From;
use std::fmt::Display;

/// Enumeration representing a single bit.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Bit {
    Zero,
    One,
}

macro_rules! bit_from_impl {
    ($($t:ty)*) => ($(
        impl From<Bit> for $t {
            fn from(bit: Bit) -> $t {
                match bit {
                    Bit::Zero => 0,
                    Bit::One => 1
                }
            }
        }

        impl From<$t> for Bit {
            fn from(u: $t) -> Bit {
                match u {
                    0 => Bit::Zero,
                    _ => Bit::One
                }
            }
        }
    )*)
}

impl From<Bit> for bool {
    fn from(bit: Bit) -> bool {
        match bit {
            Bit::Zero => false,
            Bit::One => true,
        }
    }
}

impl From<bool> for Bit {
    fn from(b: bool) -> Bit {
        match b {
            false => Bit::Zero,
            true => Bit::One,
        }
    }
}

bit_from_impl! {u8 u16 u32 u64 u128 usize}

impl Display for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bit::Zero => f.write_str("0"),
            Bit::One => f.write_str("1"),
        }
    }
}
