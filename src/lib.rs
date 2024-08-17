//! This crate is for manipulating and doing arithmetics on bit vectors of fixed but arbitrary size.
//! They are meant to behave like CPU hardware registers with wrap-around on overflow.
//!
//! This crate provides multiple implementations relying on different memory management strategies.
//!
//! * The [`Bvf`] implementation uses statically sized arrays of unsigned integers as storage
//!   and thus has a fixed capacity but does not require dynamic memory allocation.
//! * The [`Bvd`] implementation uses a dynamically allocated array of
//!   integers as storage and therefore has a dynamic capacity and support resizing operations.
//! * The [`Bv`] implementation is capable of switching at runtime between the [`Bvf`] and [`Bvd`]
//!   implementations to try to minimize dynamic memory allocations whenever possible.
//!
//! All of those implementations implement the [`BitVector`] trait and can be freely mixed together
//! and abstracted through generic traits.
//!
//! The different bit vector types represent a vector of bits where the bit at index 0 is the least
//! significant bit and the bit at index `.len() - 1` is the most significant bit. There is no
//! notion of endianness for the bit vector themselves, endianness is only involved when reading or
//! writing a bit vector from or to memory.
//!
//! Arithmetic operation can be applied to bit vectors of different types and different lengths.
//! The result will always have the type and the length of the left hand side operand. The right
//! hand side operand will be zero extended if needed. Operations will wrap-around in the case of
//! overflows. This should match the behavior of unsigned integer arithmetics on CPU registers.
//!
//! # Examples
//!
//! Bit vectors expose an API similar to Rust `std::collections::Vec`:
//! ```
//! use bva::{Bit, BitVector, Bvd};
//!
//! let mut bv = Bvd::with_capacity(128);
//! assert_eq!(bv.capacity(), 128);
//! bv.push(Bit::One);
//! bv.push(Bit::One);
//! bv.resize(16, Bit::Zero);
//! assert_eq!(bv.len(), 16);
//! assert_eq!(bv.first(), Some(Bit::One));
//! assert_eq!(bv.last(), Some(Bit::Zero));
//! let pop_count = bv.iter().fold(0u32, |acc, b| acc + u32::from(b));
//! assert_eq!(pop_count, 2);
//! ```
//!
//! Additionally, bit vector specific operations are available:
//! ```
//! use bva::{Bit, BitVector, Bv32};
//!
//! // While Bv32 has a capacity of 32 bits, it inherits the length of the u8.
//! let mut a = Bv32::try_from(0b111u8).unwrap();
//! a.rotr(2);
//! assert_eq!(a, Bv32::try_from(0b11000001u8).unwrap());
//! assert_eq!(a.get(7), Bit::One);
//! a.set(1, Bit::One);
//! assert_eq!(a, Bv32::try_from(0b11000011u8).unwrap());
//! assert_eq!(a.copy_range(1..7), Bv32::try_from(0b100001u8).unwrap());
//! ```
//!
//! Bit vectors behave like unsigned integers with wrap-around on overflow:
//! ```
//! use bva::{Bit, BitVector, Bv32};
//!
//! // Bv32 is a type alias for a Bvf with 32 bits of capacity.
//! let a = Bv32::ones(32);
//! let b = Bv32::try_from(1u32).unwrap();
//! assert_eq!(b.leading_zeros(), 31);
//! let c = a + b;
//! assert_eq!(c, Bv32::zeros(32));
//! ```
//!
//! Generic traits can be used to abstract over the different bit vector implementations:
//! ```
//! use core::ops::AddAssign;
//! use bva::{Bit, BitVector, Bv, Bvd, Bvf};
//!
//! fn fibonnaci<B: BitVector + for<'a> AddAssign<&'a B>>(n: usize) -> B {
//!     let mut f0 = B::zeros(1);
//!     let mut f1 = B::ones(1);
//!     if n == 0 {
//!         return f0;
//!     }
//!
//!     for _ in 1..n {
//!         // Avoid overflow
//!         f0.resize(f1.significant_bits() + 1, Bit::Zero);
//!         // Addition is done in place
//!         f0 += &f1;
//!         // Swap f0 and f1
//!         std::mem::swap(&mut f0, &mut f1);
//!     }
//!     return f1;
//! }
//!
//! assert_eq!(fibonnaci::<Bvf<u8, 2>>(15), Bvf::<u8, 2>::try_from(610u16).unwrap());
//! assert_eq!(fibonnaci::<Bvd>(18), Bvd::from(2584u32));
//! assert_eq!(fibonnaci::<Bv>(19), Bv::from(4181u32));
//! ```

#![warn(missing_docs)]
#![allow(
    clippy::suspicious_arithmetic_impl,
    clippy::suspicious_op_assign_impl,
    clippy::comparison_chain,
    clippy::needless_range_loop
)]

use std::fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex};
use std::io::{Read, Write};
use std::ops::Range;

mod auto;
mod bit;
mod dynamic;
mod fixed;
mod iter;
mod utils;

pub use auto::Bv;
pub use bit::Bit;
pub use dynamic::Bvd;
pub use fixed::{Bv128, Bv16, Bv192, Bv256, Bv32, Bv320, Bv384, Bv448, Bv512, Bv64, Bv8, Bvf};
pub use iter::BitIterator;
use utils::{IArray, IArrayMut};

/// The endianness of an I/O operation.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Endianness {
    /// Little Endian ordering.
    Little,
    /// Big Endian ordering.
    Big,
}

/// Errors which can happen during convertion operations.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ConvertionError {
    /// The underlying bit vector type did not have enough capacity to perform the operation.
    NotEnoughCapacity,
    /// The source data format is invalid at the specified offset.
    InvalidFormat(usize),
}

impl Display for ConvertionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConvertionError::NotEnoughCapacity => write!(
                f,
                "The bit vector did not have enough capacity to perform the convertion"
            ),
            ConvertionError::InvalidFormat(pos) => write!(
                f,
                "The bit vector convertion method encountered an error at index {}",
                pos
            ),
        }
    }
}

impl std::error::Error for ConvertionError {}

/// A trait containing common bit vector operations.
pub trait BitVector:
    Binary
    + Clone
    + Debug
    + Display
    + Eq
    + IArray
    + IArrayMut
    + LowerHex
    + Octal
    + Ord
    + PartialEq
    + PartialOrd
    + Sized
    + UpperHex
{
    /// Construct an empty pre-allocated with enough capacity to store `length` bits.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    ///
    /// ```
    /// use bva::{BitVector, Bvd};
    ///
    /// let a = Bvd::with_capacity(1024);
    /// assert_eq!(a.capacity(), 1024);
    /// ```
    fn with_capacity(length: usize) -> Self;

    /// Construct a bit vector made of `length` 0 bits.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::zeros(1024);
    ///
    /// assert_eq!(a.len(), 1024);
    /// assert_eq!(a.leading_zeros(), 1024);
    /// assert_eq!(a.trailing_zeros(), 1024);
    /// ```
    fn zeros(length: usize) -> Self;

    /// Construct a bit vector made of `length` 1 bits.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    ///
    /// ```
    /// use bva::{BitVector, Bvd};
    ///
    /// let a = Bvd::ones(1024);
    ///
    /// assert_eq!(a.len(), 1024);
    /// assert_eq!(a.leading_ones(), 1024);
    /// assert_eq!(a.trailing_ones(), 1024);
    /// ```
    fn ones(length: usize) -> Self;

    /// Construct a bit vector by repeating a bit `lenth` times.
    ///
    /// ```
    /// use bva::{BitVector, Bit, Bv};
    ///
    /// assert_eq!(
    ///     Bv::repeat(Bit::Zero, 1024),
    ///     Bv::zeros(1024)
    /// );
    ///
    /// assert_eq!(
    ///     Bv::repeat(Bit::One, 1024),
    ///     Bv::ones(1024)
    /// );
    /// ```
    fn repeat(bit: Bit, length: usize) -> Self {
        if bit == Bit::Zero {
            Self::zeros(length)
        } else {
            Self::ones(length)
        }
    }

    /// Return the capacity of the bit vector in bits.
    ///
    /// ```
    /// use bva::{BitVector, Bv64};
    ///
    /// let a = Bv64::zeros(0);
    /// assert_eq!(a.capacity(), 64);
    /// ```
    fn capacity(&self) -> usize;

    /// Return the length of the bit vector in bits.
    ///
    /// ```
    /// use bva::{BitVector, Bv64};
    ///
    /// let a = Bv64::zeros(11);
    /// assert_eq!(a.len(), 11);
    /// ```
    fn len(&self) -> usize;

    /// Return wether the bit vector is empty or not.
    ///
    /// ```
    /// use bva::{BitVector, Bv64};
    ///
    /// let a = Bv64::zeros(0);
    /// assert_eq!(a.is_empty(), true);
    /// ```
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Construct a bit vector from a binary string made of `'0'` and `'1'`.
    /// Return `None` if the string is invalid or exceed the maximum capacity.
    ///
    /// ```
    /// use bva::{BitVector, Bv16};
    ///
    /// let a = Bv16::from_binary("101010101").unwrap();
    /// assert_eq!(a, Bv16::try_from(0b101010101u16).unwrap());
    /// ```
    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError>;

    /// Construct a bit vector from a hex string made of lower case or upper case hexadecimal
    /// characters (mixed case is accepted).
    /// Return `None` if the string is invalid or exceed the maximum capacity.
    ///
    /// ```
    /// use bva::{BitVector, Bvf};
    ///
    /// let a = Bvf::<u64, 4>::from_hex("101112131415161718191a1b1c1d1e1f").unwrap();
    /// assert_eq!(a, Bvf::<u64, 4>::try_from(0x101112131415161718191a1b1c1d1e1fu128).unwrap());
    /// ```
    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError>;

    /// Construct a bit vector from `bytes` according to the specified `endianness`.
    /// Will panic if the length of `bytes` is larger than the maximum capacity.
    ///
    /// ```
    /// use bva::{BitVector, Bv64, Endianness};
    ///
    /// let a = Bv64::from_bytes(&[0x12, 0x34, 0x56, 0x78], Endianness::Big).unwrap();
    /// assert_eq!(a, Bv64::try_from(0x12345678u64).unwrap());
    /// ```
    fn from_bytes<B: AsRef<[u8]>>(
        bytes: B,
        endianness: Endianness,
    ) -> Result<Self, ConvertionError>;

    /// Construct a new vector of bytes from the bit vector according to the specified `endianness`.
    /// If the length is not a multiple of 8 bits, he most significant byte will be padded with `'0'`.
    ///
    /// ```
    /// use bva::{BitVector, Bv64, Endianness};
    ///
    /// let a = Bv64::try_from(0x12345678u32).unwrap();
    /// assert_eq!(a.to_vec(Endianness::Little), vec![0x78, 0x56, 0x34, 0x12]);
    fn to_vec(&self, endianness: Endianness) -> Vec<u8>;

    /// Construct a bit vector by reading `length` bits from a type implementing `Read` and
    /// arrange them according to the specified `endianness`. If `length` is not a multiple of 8,
    /// the bits remaining in the most signigicant byte will be dropped.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn read<R: Read>(
        reader: &mut R,
        length: usize,
        endianness: Endianness,
    ) -> std::io::Result<Self>;

    /// Write the bit vector to a type implementing `Write` and according to the specified
    /// `endianness`. If the length is not a multiple of 8 bits, the most significant byte will be
    /// padded with `'0'`.
    fn write<W: Write>(&self, writer: &mut W, endianness: Endianness) -> std::io::Result<()>;

    /// Return the bit at `index`.
    /// Will panic if `index` is out of bound.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv64};
    ///
    /// let a = Bv64::try_from(0b101010101u64).unwrap();
    /// assert_eq!(a.get(2), Bit::One);
    /// assert_eq!(a.get(5), Bit::Zero);
    /// ```
    fn get(&self, index: usize) -> Bit;

    /// Set the bit at `index`.
    /// Will panic if `index` is out of bound.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv64};
    ///
    /// let mut a = Bv64::try_from(0b101010101u64).unwrap();
    /// a.set(2, Bit::Zero);
    /// assert_eq!(a, Bv64::try_from(0b101010001u64).unwrap());
    /// ```
    fn set(&mut self, index: usize, bit: Bit);

    /// Get the first (least significant) bit of this bit vector.
    /// Return None if the bit vector is empty.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv};
    ///
    /// let a = Bv::from(0b01010101u64);
    /// assert_eq!(a.first(), Some(Bit::One));
    /// ```
    fn first(&self) -> Option<Bit> {
        if self.len() > 0 {
            Some(self.get(0))
        } else {
            None
        }
    }

    /// Get the last (most significant) bit of this bit vector.
    /// Return None if the bit vector is empty.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv};
    ///
    /// let a = Bv::from(0b01010101u64);
    /// assert_eq!(a.last(), Some(Bit::Zero));
    /// ```
    fn last(&self) -> Option<Bit> {
        if self.len() > 0 {
            Some(self.get(self.len() - 1))
        } else {
            None
        }
    }

    /// Slice the bit vector using the specified range and copy those bits in a new bit vector.
    /// Will panic if `range` start or end are out of bound.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0b101010101u64);
    /// assert_eq!(a.copy_range(1..4), Bv::from(0b010u64));
    /// ```
    fn copy_range(&self, range: Range<usize>) -> Self;

    /// Push a bit at the end of the bit vector as the most significant bit.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv};
    ///
    /// let mut a = Bv::from(0b01010101u8);
    /// a.push(Bit::One);
    /// assert_eq!(a, Bv::from(0b101010101u64));
    /// ```
    fn push(&mut self, bit: Bit);

    /// Pop a bit from the end of the bit vector.
    /// Return None if the bit vector is empty.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv};
    ///
    /// let mut a = Bv::from(0b10101010u8);
    /// assert_eq!(a.pop(), Some(Bit::One));
    /// assert_eq!(a.pop(), Some(Bit::Zero));
    /// assert_eq!(a, Bv::from(0b101010u8));
    /// ```
    fn pop(&mut self) -> Option<Bit>;

    /// Resize the bit vector in place so that its length is equal to `new_length`.
    /// This will either truncate or extend the bit vector. If it is extended, new bits are filled
    /// with `bit`.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv};
    ///
    /// let mut a = Bv::zeros(8);
    /// a.resize(10, Bit::One);
    /// assert_eq!(a, Bv::from(0b1100000000u16));
    /// ```
    fn resize(&mut self, new_length: usize, bit: Bit);

    /// Resize this bit vector using the most significant bit as a sign bit so that its length
    /// is equal to `new_length`. If `new_length` is smaller than the current length, this method
    /// does nothing.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let mut a = Bv::zeros(8);
    /// a -= 1u8;
    /// a.sign_extend(16);
    /// assert_eq!(a, Bv::from(0b1111_1111_1111_1111u16));
    /// ```
    fn sign_extend(&mut self, new_length: usize) {
        if new_length > self.len() {
            let sign = match self.len() {
                0 => Bit::Zero,
                l => self.get(l - 1),
            };
            self.resize(new_length, sign);
        }
    }

    /// Append the `suffix` bit vector at the end (most significant part) of this bit vector.
    /// Will panic if there is not enough capacity and this is a fixed variant.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let mut a = Bv::from(0u8);
    /// a.append(&Bv::from(1u8));
    /// assert_eq!(a, Bv::from(0b1_0000_0000u16));
    /// ```
    fn append<B: BitVector>(&mut self, suffix: &B);

    /// Prepend the `prefix` bit vector at the beginning (least significant part) of this bit vector.
    /// Will panic if there is not enough capacity and this is a fixed variant.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let mut a = Bv::from(1u8);
    /// a.prepend(&Bv::from(0u8));
    /// assert_eq!(a, Bv::from(0b1_0000_0000u16));
    /// ```
    fn prepend<B: BitVector>(&mut self, prefix: &B);

    /// Shift the bits by one to the left.
    /// The rightmost bit is set to `bit` and the leftmost bit is returned.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv};
    ///
    /// let mut a = Bv::from(0b1010_1010u8);
    /// assert_eq!(a.shl_in(Bit::Zero), Bit::One);
    /// assert_eq!(a, Bv::from(0b0101_0100u8));
    /// ```
    fn shl_in(&mut self, bit: Bit) -> Bit;

    /// Shift the bits by one to the right.
    /// The leftmost bit is set to `bit` and the rightmost bit is returned.
    ///
    /// ```
    /// use bva::{Bit, BitVector, Bv};
    ///
    /// let mut a = Bv::from(0b1010_1010u8);
    /// assert_eq!(a.shr_in(Bit::One), Bit::Zero);
    /// assert_eq!(a, Bv::from(0b1101_0101u8));
    fn shr_in(&mut self, bit: Bit) -> Bit;

    /// Rotate the bits to the left by `rot` positions.
    /// Will panic if the rotation amount is larger than this bit vector length.
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let mut a = Bv::from(0b1111_0000u8);
    /// a.rotl(2);
    /// assert_eq!(a, Bv::from(0b1100_0011u8));
    fn rotl(&mut self, rot: usize);

    /// Rotate the bits to the right by `rot` positions.
    /// Will panic if the rotation amount is larger than this bit vector length.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let mut a = Bv::from(0b1111u8);
    /// a.rotr(3);
    /// assert_eq!(a, Bv::from(0b1110_0001u8));
    /// ```
    fn rotr(&mut self, rot: usize);

    /// Return the number of leading (most significant) zeros in the bit vector.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0b0000_0001u8);
    /// assert_eq!(a.leading_zeros(), 7);
    /// ```
    fn leading_zeros(&self) -> usize;

    /// Return the number of leading (most significant) ones in the bit vector.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0b1111_1110u8);
    /// assert_eq!(a.leading_ones(), 7);
    /// ```
    fn leading_ones(&self) -> usize;

    /// Return the number of trailing (least significant) zeros in the bit vector.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0b1000_0000u8);
    /// assert_eq!(a.trailing_zeros(), 7);
    /// ```
    fn trailing_zeros(&self) -> usize;

    /// Return the number of trailing (least significant) ones in the bit vector.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0b0111_1111u8);
    /// assert_eq!(a.trailing_ones(), 7);
    /// ```
    fn trailing_ones(&self) -> usize;

    /// Return the number of significant bits in the bit vector.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0b0000_1001u8);
    /// assert_eq!(a.significant_bits(), 4);
    /// ```
    fn significant_bits(&self) -> usize {
        self.len() - self.leading_zeros()
    }

    /// Return whether the bit vector is all zeros.
    /// By convention, the empty bit vector is considered to be zero.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0u8);
    /// assert!(a.is_zero());
    /// ```
    fn is_zero(&self) -> bool;

    /// Divide by another bit vector and return the quotient and the remainder.
    /// Will panic if the divisor is zero.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0xDEADBEEFu32);
    /// let b = Bv::from(0xEA7u32);
    /// let (q, r) = a.div_rem(&b);
    /// assert_eq!(q, Bv::from(0xF328Eu32));
    /// assert_eq!(r, Bv::from(0x4Du32));
    /// ```
    fn div_rem<B: BitVector>(&self, divisor: &B) -> (Self, Self)
    where
        Self: for<'a> TryFrom<&'a B, Error: std::fmt::Debug>;

    /// Construct an iterator over the bits of the bit vector, from the least
    /// to the most significant bit.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let a = Bv::from(0b1010u8);
    ///
    /// for b in a.iter() {
    ///    println!("{}", b);
    /// }
    /// ```
    fn iter(&self) -> BitIterator<'_, Self>;
}

#[cfg(test)]
mod tests;
