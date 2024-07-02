//! Crate for manipulating bit vectors and doing arithmetic on arbitrarily sized bit vectors.
//!
//! This crate emphasizes optimizing storage by providing alternative storage options.
//! The module [`fixed`] contains implementations using unsigned integers as storage and thus
//! has a fixed capacity. The module [`dynamic`] contains an implementation using dynamically
//! allocated array of integers as storage and therefore has a dynamic capacity. The module
//! [`auto`] contains an implementation capable of switching at runtime between a fixed or
//! dynamic capacity implementation to try to minimize dynamic memory allocations.
//! All of those implementations implement the [`BitVector`] trait and can be freely mixed together
//! and converted into each other.
//!
//! The different bit vector types represent a vector of bits where the bit at index 0 is the least
//! significant bit and the bit at index `.len() - 1` is the most significant bit. There is no
//! notion of endianness for the bit vector themselves, endianness is only involved when reading or
//! writing a bit vector to or from memory or storage.
//!
//! Arithmetic operation can be applied to bit vectors of different length. The result will always
//! have the length of the longest operand and the smallest operand will be zero extended for the
//! operation. This should match the most intuitive behavior in most cases except when manipulating
//! bit vector supposed to have a sign bit.

#![allow(
    clippy::suspicious_arithmetic_impl,
    clippy::suspicious_op_assign_impl,
    clippy::upper_case_acronyms,
    clippy::comparison_chain,
    clippy::needless_range_loop
)]

use std::fmt::{Binary, Debug, Display, LowerHex, Octal, UpperHex};
use std::io::{Read, Write};
use std::ops::Range;

pub mod auto;
pub mod bit;
pub mod dynamic;
pub mod fixed;
pub mod iter;
mod utils;

use bit::Bit;
use iter::BitIterator;

/// An enumeration representing the endianness of an I/O or memory operation.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Endianness {
    /// Little Endian ordering: bytes are stored from the least significant byte to the most significant byte.
    LE,
    /// big Endian ordering: bytes are stored from the most significant byte to the least significant byte.
    BE,
}

/// An enumeration representing errors which can arise from convertion operation (`from_hex`, `from_binary`, `from_bytes`).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ConvertionError {
    /// The underlying BitVector type did not have enough capacity to perform the operation.
    NotEnoughCapacity,
    /// The source data format is invalid at the specified offset.
    InvalidFormat(usize),
}

impl Display for ConvertionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConvertionError::NotEnoughCapacity => write!(
                f,
                "Bit vector did not have enough capacity to perform the conversion"
            ),
            ConvertionError::InvalidFormat(pos) => write!(
                f,
                "Bit vector conversion method encountered an error at symbol {}",
                pos
            ),
        }
    }
}

impl std::error::Error for ConvertionError {}

/// A trait representing common bit vector operations.
pub trait BitVector:
    Sized
    + Clone
    + Debug
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Display
    + Binary
    + Octal
    + LowerHex
    + UpperHex
{
    /// Construct an empty pre-allocated with enough capacity to store `length` bits.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn with_capacity(length: usize) -> Self;

    /// Construct a bit vector made of `length` 0 bits.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn zeros(length: usize) -> Self;

    /// Construct a bit vector made of `length` 1 bits.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn ones(length: usize) -> Self;

    /// Construct a bit vector from a binary string made of `'0'` and `'1'`.
    /// Return `None` if the string is invalid or exceed the maximum capacity.
    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError>;

    /// Construct a bit vector from a hex string made of lower case or upper case hexadecimal
    /// characters (mixed case is accepted).
    /// Return `None` if the string is invalid or exceed the maximum capacity.
    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError>;

    /// Construct a bit vector from `bytes` according to the specified `endianness`.
    /// Will panic if the length of `bytes` is larger than the maximum capacity.
    fn from_bytes<B: AsRef<[u8]>>(
        bytes: B,
        endianness: Endianness,
    ) -> Result<Self, ConvertionError>;

    /// Construct a new vector of bytes from the bit vector according to the specified `endianness`.
    /// If the length is not a multiple of 8 bits, he highest weight bits will be padded with `'0'`.
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
    fn get(&self, index: usize) -> Bit;

    /// Set the bit at `index`.
    /// Will panic if `index` is out of bound.
    fn set(&mut self, index: usize, bit: Bit);

    /// Slice the bit vector using the specified range and copy those bits in a new bit vector.
    /// Will panic if `range` start or end are out of bound.
    fn copy_range(&self, range: Range<usize>) -> Self;

    /// Push a bit at the end of the bit vector as the most significant bit.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn push(&mut self, bit: Bit);

    /// Pop a bit from the end of the bit vector.
    /// Return None if the bit vector is empty.
    fn pop(&mut self) -> Option<Bit>;

    /// Resize the bit vector in place so that its length is equal to `new_length`.
    /// This will either truncate or extend the bit vector. If it is extended, new bits are filled
    /// with `bit`.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn resize(&mut self, new_length: usize, bit: Bit);

    /// Shift the bits by one to the left.
    /// The rightmost bit is set to `bit` and the leftmost bit is returned.
    fn shl_in(&mut self, bit: Bit) -> Bit;

    /// Shift the bits by one to the right.
    /// The leftmost bit is set to `bit` and the rightmost bit is returned.
    fn shr_in(&mut self, bit: Bit) -> Bit;

    // Rotate the bits to the left by `rot` positions.
    // Will panic if the rotation amount is larger than this bit vector length.
    fn rotl(&mut self, rot: usize);

    // Rotate the bits to the right by `rot` positions.
    // Will panic if the rotation amount is larger than this bit vector length.
    fn rotr(&mut self, rot: usize);

    /// Return the cpacity of the bit vector in bits.
    fn capacity(&self) -> usize;

    /// Return the length of the bit vector in bits.
    fn len(&self) -> usize;

    /// Return wether the bit vector is empty or not.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn iter(&self) -> BitIterator<'_, Self>;
}

#[cfg(test)]
mod tests;
