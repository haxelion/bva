use std::ops::Range;

use crate::{Bit, BitVector};

/// An iterator over the bits of a [`BitVector`].
pub struct BitIterator<'a, B: BitVector> {
    bv: &'a B,
    range: Range<usize>,
}

impl<'a, B: BitVector> BitIterator<'a, B> {
    pub(crate) fn new(bv: &'a B) -> Self {
        Self {
            bv,
            range: 0..bv.len(),
        }
    }
}

impl<B: BitVector> Iterator for BitIterator<'_, B> {
    type Item = Bit;

    fn next(&mut self) -> Option<Self::Item> {
        if self.range.start < self.range.end {
            let bit = self.bv.get(self.range.start);
            self.range.start += 1;
            Some(bit)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.range.end - self.range.start;
        (remaining, Some(remaining))
    }

    fn count(self) -> usize {
        self.range.end - self.range.start
    }

    fn last(self) -> Option<Self::Item> {
        if self.range.start < self.range.end {
            Some(self.bv.get(self.range.end - 1))
        } else {
            None
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if self.range.start + n < self.range.end {
            let bit = self.bv.get(self.range.start + n);
            self.range.start += n + 1;
            Some(bit)
        } else {
            self.range.start = self.range.end;
            None
        }
    }
}

impl<B: BitVector> DoubleEndedIterator for BitIterator<'_, B> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.range.start < self.range.end {
            self.range.end -= 1;
            Some(self.bv.get(self.range.end))
        } else {
            None
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if self.range.start + n < self.range.end {
            self.range.end -= n + 1;
            Some(self.bv.get(self.range.end))
        } else {
            self.range.end = self.range.start;
            None
        }
    }
}
