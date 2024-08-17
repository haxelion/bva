//! Implementation of the [`Bit`] type.
//!
//! This module contains a more natural representation for bits in the form of an enumeration.
//!
//! # Examples
//!
//! ```
//! use bva::Bit;
//!
//! assert_eq!(Bit::Zero, 0u8.into());
//! assert_eq!(true, Bit::One.into());
//! ```

use std::fmt::Display;

/// A single bit.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Bit {
    /// The bit `0`.
    Zero,
    /// The bit `1`.
    One,
}

macro_rules! bit_from_impl {
    ($($t:ty)*) => ($(
        impl From<Bit> for $t {
            /// Returns `0` if `bit` is `Bit::Zero` and `1` if `bit` is `Bit::One`.
            fn from(bit: Bit) -> $t {
                match bit {
                    Bit::Zero => 0,
                    Bit::One => 1
                }
            }
        }

        impl From<$t> for Bit {
            /// Returns `Bit::Zero` if `u` is `0` and `Bit::One` for any other value of `u`.
            fn from(u: $t) -> Bit {
                match u {
                    0 => Bit::Zero,
                    _ => Bit::One
                }
            }
        }
    )*)
}

bit_from_impl! {u8 u16 u32 u64 u128 usize}

impl From<Bit> for bool {
    /// Returns `false` if `bit` is `Bit::Zero` and `true` if `bit` is `Bit::One`.
    fn from(bit: Bit) -> bool {
        match bit {
            Bit::Zero => false,
            Bit::One => true,
        }
    }
}

impl From<bool> for Bit {
    /// Returns `Bit::Zero` if `b` is `false` and `Bit::One` if `b` is `true`.
    fn from(b: bool) -> Bit {
        match b {
            false => Bit::Zero,
            true => Bit::One,
        }
    }
}

impl Display for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bit::Zero => f.write_str("0"),
            Bit::One => f.write_str("1"),
        }
    }
}
