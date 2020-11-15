use std::fmt::{Binary, Display, Debug, LowerHex, UpperHex};
use std::io::{Read, Write};
use std::ops::Range;

pub mod bit;
pub mod fixed;
pub mod dynamic;

use bit::Bit;

pub enum Endianness {
    LE,
    BE
}

/// A trait representing common bit vector operations
pub trait BitVector: Sized + Clone + Debug + PartialEq + Eq + Display + Binary + LowerHex + UpperHex {
    /// Construct a bit vector made of `len` 0 bits.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn zeros(len: usize) -> Self;

    /// Construct a bit vector made of `len` 1 bits.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn ones(len: usize) -> Self;

    /// Construct a bit vector from a binary string made of `'0'` and `'1'`.
    /// Return `None` if the string is invalid or exceed the maximum capacity.
    fn from_binary<S: AsRef<str>>(string: S) -> Option<Self>;

    /// Construct a bit vector from a hex string made of lower case or upper case hexadecimal 
    /// characters (mixed case is accepted).
    /// Return `None` if the string is invalid or exceed the maximum capacity.
    fn from_hex<S: AsRef<str>>(string: S) -> Option<Self>;

    /// Construct a bit vector from `bytes` according to the specified `endianness`.
    /// Will panic if the length of `bytes` is larger than the maximum capacity.
    fn from_bytes<B: AsRef<[u8]>>(bytes: B, endianness: Endianness) -> Self;

    /// Construct a bit vector by reading `num_bytes` bytes from a type implementing `Read` and 
    /// arrange them according to the specified `endianness`. If `length` is not a multiple of 8,
    /// the bits remaining in the highest weight byte will be dropped.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn read<R: Read>(reader: &mut R, length: usize, endianness: Endianness) -> std::io::Result<Self>;

    /// Write a bit vector to a type implementing `Write` and according to the specified 
    /// `endianness`. If the length is not a multiple of 8, he highest weight byte will be padded 
    /// with `'0'`.
    fn write<W: Write>(&self, writer: &mut W, endianness: Endianness) -> std::io::Result<()>;

    /// Return the bit at `index`.
    /// Will panic if `index` is out of bound.
    fn get(&self, index: usize) -> Bit;

    /// Set the bit at `index`.
    /// Will panic if `index` is out of bound.
    fn set(&mut self, index: usize, bit: Bit);

    /// Slice the bit vector using the specified range and copy those bits in a new bit vector.
    /// Will panic if `range` start or end are out of bound.
    fn copy_slice(&self, range: Range<usize>) -> Self;

    /// Push a bit at the end of the bit vector as the most significant bit.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn push(&mut self, bit: Bit);

    /// Pop a bit from the end of the bit vector.
    /// Return None if the bit vector is empty.
    fn pop(&mut self) -> Option<Bit>;

    /// Resize the bit vector in place so that its length is equal to `new_len`.
    /// This will either truncate or extend the bit vector. If it is extended, new bits are filled 
    /// with `bit`.
    /// Will panic if there is not enough capacity and it is a fixed variant.
    fn resize(&mut self, new_len: usize, bit: Bit);

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

    /// Return the length of the bit vector in bits.
    fn len(&self) -> usize;
}

#[cfg(test)]
mod tests;