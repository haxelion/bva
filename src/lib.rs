use std::ops::Range;

pub mod bit;
pub mod fixed;

use bit::Bit;

/// A trait representing common bit vector operations
pub trait BitVector: Sized {
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