use std::fmt::{Binary, Display, LowerHex, Octal, UpperHex};
use std::io::{Read, Write};
use std::iter::repeat;
use std::mem::size_of;

use crate::{Bit, BitVector, Endianness};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct BVN {
    data: Box<[usize]>,
    length: usize
}

impl BVN {
    const BYTE_UNIT: usize = size_of::<usize>();
    const NIBBLE_UNIT: usize = size_of::<usize>() * 2;
    const SEMI_NIBBLE_UNIT: usize = size_of::<usize>() * 4;
    const BIT_UNIT: usize = size_of::<usize>() * 8;

    fn capacity_from_byte_len(byte_length: usize) -> usize {
        (byte_length + size_of::<usize>() - 1) / size_of::<usize>()
    }

    fn capacity_from_bit_len(bit_length: usize) -> usize {
        Self::capacity_from_byte_len((bit_length + 7) / 8)
    }

    fn mask(length: usize) -> usize {
        usize::MAX.checked_shr((Self::BIT_UNIT - length) as u32).unwrap_or(0)
    }

    pub fn reserve(&mut self, additional: usize) {
        let new_length = self.length + additional;
        if Self::capacity_from_bit_len(new_length) > self.data.len() {
            // TODO: in place reallocation
            let mut new_data: Vec<usize> = repeat(0usize).take(Self::capacity_from_bit_len(new_length)).collect();
            for i in 0..self.data.len() {
                new_data[i] = self.data[i];
            }
            self.data = new_data.into_boxed_slice();
        }
    }
}

impl BitVector for BVN {
    fn zeros(length: usize) -> Self {
        let mut v: Vec<usize> = repeat(0).take(Self::capacity_from_bit_len(length)).collect();
        BVN {
            data: v.into_boxed_slice(),
            length
        }
    }

    fn ones(length: usize) -> Self {
        let mut v: Vec<usize> = repeat(usize::MAX).take(Self::capacity_from_bit_len(length)).collect();
        if let Some(l) = v.last_mut() {
            *l &= Self::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }

        BVN {
            data: v.into_boxed_slice(),
            length
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
        let length = string.as_ref().chars().count();
        let offset = (Self::NIBBLE_UNIT - length % Self::NIBBLE_UNIT) % Self::NIBBLE_UNIT;
        let mut data: Vec<usize> = repeat(0usize).take(Self::capacity_from_byte_len((length + 1) / 2)).collect();

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = data.len() - 1 - (i + offset) / Self::NIBBLE_UNIT;
            data[j] = (data[j] << 4) | match c.to_digit(16) {
                Some(d) => d as usize,
                None => return None
            };
        }  
        Some(BVN {
            data: data.into_boxed_slice(),
            length: length * 4
        })
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

    fn to_vec(&self, endianness: Endianness) -> Vec<u8> {
        let num_bytes = (self.length + 7) / 8;
        let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
        match endianness {
            Endianness::LE => {
                for i in 0..num_bytes {
                    buf[i] = (self.data[i / Self::BYTE_UNIT] >> ((i % Self::BYTE_UNIT) * 8) & 0xff) as u8;
                }
            },
            Endianness::BE => {
                for i in 0..num_bytes {
                    buf[num_bytes - i - 1] = (self.data[i / Self::BYTE_UNIT] >> ((i % Self::BYTE_UNIT) * 8) & 0xff) as u8;
                }
            }
        }
        return buf;
    }

    fn read<R: Read>(reader: &mut R, length: usize, endianness: Endianness) -> std::io::Result<Self> {
        // TODO: double allocation could be reduced to a single one with endianness switch in place
        let num_bytes = (length + 7) / 8;
        let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
        reader.read_exact(&mut buf[..])?;
        let mut bv = Self::from_bytes(&buf[..], endianness);
        if let Some(l) = bv.data.last_mut() {
            *l &= Self::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }
        bv.length = length ;
        return Ok(bv);
    }

    fn write<W: Write>(&self, writer: &mut W, endianness: Endianness) -> std::io::Result<()> {
        return writer.write_all(self.to_vec(endianness).as_slice());
    }

    fn get(&self, index: usize) -> Bit {
        debug_assert!(index < self.length);
        (self.data[index / Self::BIT_UNIT] >> (index % Self::BIT_UNIT) & 1).into()
    }

    fn set(&mut self, index: usize, bit: Bit) {
        debug_assert!(index < self.length);
        self.data[index / Self::BIT_UNIT] = 
            (self.data[index / Self::BIT_UNIT] & !(1 << (index % Self::BIT_UNIT))) | 
            ((bit as usize) << (index % Self::BIT_UNIT));
    }

    fn copy_slice(&self, range: std::ops::Range<usize>) -> Self {
        debug_assert!(range.start < self.len() && range.end <= self.len());
        let length = range.end - usize::min(range.start, range.end);
        let mut data: Vec<usize> = repeat(0usize).take(Self::capacity_from_bit_len(length)).collect();
        let offset = range.start / Self::BIT_UNIT;
        let slide = range.start % Self::BIT_UNIT;

        for i in 0..data.len() {
            data[i] = (self.data[i + offset] >> slide) | 
                self.data.get(i + offset + 1).unwrap_or(&0).checked_shl((Self::BIT_UNIT - slide) as u32).unwrap_or(0);
        }
        if let Some(l) = data.last_mut() {
            *l &= Self::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }

        BVN {
            data: data.into_boxed_slice(),
            length
        }
    }

    fn push(&mut self, bit: Bit) {
        self.reserve(1);
        self.length += 1;
        self.set(self.length - 1, bit);
    }

    fn pop(&mut self) -> Option<Bit> {
        if self.length == 0 {
            return None;
        }
        let bit = self.get(self.length - 1);
        self.length -= 1;
        return Some(bit);
    }

    fn resize(&mut self, new_length: usize, bit: Bit) {
        if new_length < self.length {
            for i in (new_length / Self::BIT_UNIT + 1)..Self::capacity_from_bit_len(self.length) {
                self.data[i] = 0;
            }
            if let Some(l) = self.data.get_mut(new_length / Self::BIT_UNIT) {
                *l &= Self::mask(new_length % Self::BIT_UNIT);
            }
            self.length = new_length;
        }
        else if new_length > self.length {
            let sign_pattern = match bit {
                Bit::Zero => usize::MIN,
                Bit::One  => usize::MAX,
            };
            self.reserve(new_length - self.length);
            if let Some(l) = self.data.get_mut(self.length / Self::BIT_UNIT) {
                *l |= sign_pattern & !Self::mask(self.length % Self::BIT_UNIT);
            }
            for i in (self.length / Self::BIT_UNIT + 1)..Self::capacity_from_bit_len(new_length) {
                self.data[i] = sign_pattern;
            }
            if let Some(l) = self.data.get_mut(new_length / Self::BIT_UNIT) {
                *l &= Self::mask(new_length % Self::BIT_UNIT);
            }
            self.length = new_length;
        }
    }

    fn shl_in(&mut self, bit: Bit) -> Bit {
        let mut carry = bit;
        for i in 0..(self.length / Self::BIT_UNIT) {
            let b = self.data[i] >> (Self::BIT_UNIT - 1) & 1;
            self.data[i] = self.data[i] << 1 | carry as usize;
            carry = b.into();
        }
        if self.length % Self::BIT_UNIT != 0 {
            let i = self.length / Self::BIT_UNIT;
            let b = self.data[i] >> (self.length % Self::BIT_UNIT - 1) & 1;
            self.data[i] = (self.data[i] << 1 | carry as usize) & Self::mask(self.length % Self::BIT_UNIT);
            carry = b.into();
        }
        return carry;
    }

    fn shr_in(&mut self, bit: Bit) -> Bit {
        let mut carry = bit;
        if self.length % Self::BIT_UNIT != 0 {
            let i = self.length / Self::BIT_UNIT;
            let b = self.data[i] & 1;
            self.data[i] = self.data[i] >> 1 | (carry as usize) << (self.length % Self::BIT_UNIT - 1);
            carry = b.into();
        }
        for i in (0..(self.length / Self::BIT_UNIT)).rev() {
            let b = self.data[i] & 1;
            self.data[i] = self.data[i] >> 1 | (carry as usize) << (Self::BIT_UNIT - 1);
            carry = b.into();
        }
        return carry;
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
        const NIBBLE: [char;16] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'];
        let length = (self.length + 3) / 4;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            s.push(NIBBLE[(self.data[i / Self::NIBBLE_UNIT] >> ((i % Self::NIBBLE_UNIT) * 4) & 0xf) as usize]);
        }
        if f.alternate() {
            return write!(f, "0x{}", s.as_str());
        }
        else {
            return write!(f, "{}", s.as_str());
        }
    }
}

impl UpperHex for BVN {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const NIBBLE: [char;16] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'];
        let length = (self.length + 3) / 4;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            s.push(NIBBLE[(self.data[i / Self::NIBBLE_UNIT] >> ((i % Self::NIBBLE_UNIT) * 4) & 0xf) as usize]);
        }
        if f.alternate() {
            return write!(f, "0x{}", s.as_str());
        }
        else {
            return write!(f, "{}", s.as_str());
        }
    }
}

impl Octal for BVN {
fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const SEMI_NIBBLE: [char;8] = ['0', '1', '2', '3', '4', '5', '6', '7'];
        let length = (self.length + 2) / 3;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            s.push(SEMI_NIBBLE[(self.data[i / Self::SEMI_NIBBLE_UNIT] >> ((i % Self::SEMI_NIBBLE_UNIT) * 4) & 0xf) as usize]);
        }
        if f.alternate() {
            return write!(f, "0x{}", s.as_str());
        }
        else {
            return write!(f, "{}", s.as_str());
        }
    }
}