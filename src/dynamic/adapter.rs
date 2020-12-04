use std::convert::From;
use std::iter::{ExactSizeIterator, Iterator};
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
    idx: usize,
    data: T
}

impl<T: Streamable> USizeStream<T> {
    pub const LENGTH: usize = (size_of::<T>() + size_of::<usize>() - 1) / size_of::<usize>();

    pub fn new(t: T) -> USizeStream<T> {
        USizeStream::<T> {
            idx: 0,
            data: t
        }
    }

    pub fn bit_length(&self) -> usize {
        size_of::<T>() * 8
    }
}

impl<T: Streamable> Iterator for USizeStream<T> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.idx < Self::LENGTH {
            let r = (self.data >> (self.idx * size_of::<usize>() * 8)).static_usize_cast();
            self.idx += 1;
            return Some(r);
        }
        return None;
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (Self::LENGTH - self.idx, Some(Self::LENGTH - self.idx))
    }
}

impl<T: Streamable> ExactSizeIterator for USizeStream<T> {}