use std::fmt::{Binary, Display, LowerHex, Octal, UpperHex};
use std::io::{Read, Write};
use std::iter::repeat;
use std::mem::size_of;
use std::num::Wrapping;

use crate::{Bit, BitVector, Endianness};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct BVN {
    data: Box<[usize]>,
    length: usize
}

impl BVN {
    const BYTE_UNIT: usize = size_of::<usize>();
    const BIT_UNIT: usize = size_of::<usize>() * 8;

    fn capacity_from_byte_len(byte_len: usize) -> usize {
        (byte_len + size_of::<usize>() - 1) / size_of::<usize>()
    }

    fn capacity_from_bit_len(bit_len: usize) -> usize {
        Self::capacity_from_byte_len((bit_len + 7) / 8)
    }

    fn mask(len: usize) -> usize {
        usize::MAX.checked_shr((Self::BIT_UNIT - len) as u32).unwrap_or(0)
    }
}

impl BitVector for BVN {
    fn zeros(len: usize) -> Self {
        let mut v: Vec<usize> = repeat(0).take(Self::capacity_from_bit_len(len)).collect();
        BVN {
            data: v.into_boxed_slice(),
            length: len
        }
    }

    fn ones(len: usize) -> Self {
        let mut v: Vec<usize> = repeat(usize::MAX).take(Self::capacity_from_bit_len(len)).collect();
        if let Some(l) = v.last_mut() {
            *l &= Self::mask(len % Self::BIT_UNIT);
        }

        BVN {
            data: v.into_boxed_slice(),
            length: len
        }
    }

    fn from_binary<S: AsRef<str>>(string: S) -> Option<Self> {
        let length = string.as_ref().chars().count();
        let offset = (Self::BIT_UNIT - length % Self::BIT_UNIT) % Self::BIT_UNIT;
        let mut data: Vec<usize> = repeat(0usize).take(Self::capacity_from_bit_len(length)).collect();

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = data.len() - 1 - (i + offset) / Self::BIT_UNIT;
            data[j] = (data[j] << 1) | match c {
                '0' => 0,
                '1' => 1,
                _ => return None
            };
        }
        return Some(Self {
            data: data.into_boxed_slice(),
            length
        })
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Option<Self> {
        todo!()
    }

    fn from_bytes<B: AsRef<[u8]>>(bytes: B, endianness: Endianness) -> Self {
        let byte_length = bytes.as_ref().len();
        let mut data: Vec<usize> = repeat(0usize).take(Self::capacity_from_byte_len(byte_length)).collect();
        match endianness {
            Endianness::LE => {
                let offset = (Self::BYTE_UNIT - byte_length % Self::BYTE_UNIT) % Self::BYTE_UNIT;
                for (i, b) in bytes.as_ref().iter().rev().enumerate() {
                    let j = data.len() - 1 - (i + offset) / Self::BYTE_UNIT;
                    data[j] = (data[j] << 8) | *b as usize;
                }
            },
            Endianness::BE => {
                let offset = (Self::BYTE_UNIT - byte_length % Self::BYTE_UNIT) % Self::BYTE_UNIT;
                for (i, b) in bytes.as_ref().iter().enumerate() {
                    let j = data.len() - 1 - (i + offset) / Self::BYTE_UNIT;
                    data[j] = (data[j] << 8) | *b as usize;
                }
            }
        }
        BVN {
            data: data.into_boxed_slice(),
            length: byte_length * 8
        }
    }

    fn read<R: Read>(reader: &mut R, length: usize, endianness: Endianness) -> std::io::Result<Self> {
        todo!()
    }

    fn write<W: Write>(&self, writer: &mut W, endianness: Endianness) -> std::io::Result<()> {
        todo!()
    }

    fn get(&self, index: usize) -> Bit {
        todo!()
    }

    fn set(&mut self, index: usize, bit: Bit) {
        todo!()
    }

    fn copy_slice(&self, range: std::ops::Range<usize>) -> Self {
        todo!()
    }

    fn push(&mut self, bit: Bit) {
        todo!()
    }

    fn pop(&mut self) -> Option<Bit> {
        todo!()
    }

    fn resize(&mut self, new_len: usize, bit: Bit) {
        todo!()
    }

    fn shl_in(&mut self, bit: Bit) -> Bit {
        todo!()
    }

    fn shr_in(&mut self, bit: Bit) -> Bit {
        todo!()
    }

    fn rotl(&mut self, rot: usize) {
        todo!()
    }

    fn rotr(&mut self, rot: usize) {
        todo!()
    }

    fn len(&self) -> usize {
        self.length
    }
}

impl Binary for BVN {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::with_capacity(self.length);
        for i in (0..self.length).rev() {
            match self.data[i / (size_of::<usize>() * 8)] >> (i % (size_of::<usize>() * 8)) & 1 {
                0 => s.push('0'),
                1 => s.push('1'),
                _ => unreachable!()
            }
        }
        if f.alternate() {
            return write!(f, "0b{}", s.as_str());
        }
        else {
            return write!(f, "{}", s.as_str());
        }
    }
}

impl Display for BVN {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl LowerHex for BVN {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl UpperHex for BVN {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Octal for BVN {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}