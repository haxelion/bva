use std::iter::{ExactSizeIterator, DoubleEndedIterator, Iterator};
use std::mem::size_of;
use std::ops::{Shr, BitAnd};

pub trait Streamable: Copy + Sized + Shr<usize, Output=Self> + BitAnd {
    fn static_usize_cast(self) -> usize;
}

impl Streamable for u8 {
    fn static_usize_cast(self) -> usize {
        self as usize
    }
}
impl Streamable for u16 {
    fn static_usize_cast(self) -> usize {
        self as usize
    }
}
impl Streamable for u32 {
    fn static_usize_cast(self) -> usize {
        self as usize
    }
}
impl Streamable for u64 {
    fn static_usize_cast(self) -> usize {
        self as usize
    }
}
impl Streamable for u128 {
    fn static_usize_cast(self) -> usize {
        self as usize
    }
}
impl Streamable for usize {
    fn static_usize_cast(self) -> usize {
        self as usize
    }
}

pub struct USizeStream<T> where T: Streamable {
    front_idx: usize,
    back_idx: usize,
    data: T
}

impl<T: Streamable> USizeStream<T> {
    pub const LENGTH: usize = (size_of::<T>() + size_of::<usize>() - 1) / size_of::<usize>();

    pub fn new(t: T) -> USizeStream<T> {
        USizeStream::<T> {
            front_idx: 0,
            back_idx: Self::LENGTH,
            data: t
        }
    }

    pub fn bit_length(&self) -> usize {
        size_of::<T>() * 8
    }

    fn get(&self, idx: usize) -> usize {
        (self.data >> (idx * size_of::<usize>() * 8)).static_usize_cast()
    }
}

impl<T: Streamable> Iterator for USizeStream<T> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.front_idx < self.back_idx {
            self.front_idx += 1;
            return Some(self.get(self.front_idx - 1));
        }
        return None;
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.back_idx - self.front_idx, Some(self.back_idx - self.front_idx))
    }
}

impl<T: Streamable> ExactSizeIterator for USizeStream<T> {}

impl<T: Streamable> DoubleEndedIterator for USizeStream<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front_idx < self.back_idx {
            self.back_idx -= 1;
            return Some(self.get(self.back_idx));
        }
        return None;
    }
}