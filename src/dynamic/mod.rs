//! This module contains a dynamic capacity bit vector implementation using a dynamically allocated
//! integer array as storage.
//!
//! As the capacity is dynamic, performing operations exceeding the current capacity will result in
//! a reallocation of the internal array.

use std::cmp::Ordering;
use std::convert::{From, TryFrom};
use std::fmt::{Binary, Display, LowerHex, Octal, UpperHex};
use std::io::{Read, Write};
use std::iter::repeat;
use std::mem::size_of;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, 
    Range, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

use crate::{Bit, BitVector, ConvertError, Endianness};
use crate::fixed::{BV8, BV16, BV32, BV64, BV128};

mod adapter;

use adapter::USizeStream;

/// A bit vector with dynamic capacity.
#[derive(Clone, Debug)]
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

    /// Allocate a bit vector of length 0 but with enough capacity to store `capacity` bits.
    pub fn with_capacity(capacity: usize) -> Self {
        let data: Vec<usize> = repeat(0usize).take(Self::capacity_from_bit_len(capacity)).collect();
        BVN {
            data: data.into_boxed_slice(),
            length: 0
        }
    }

    /// Reserve will reserve room for at least `additional` bits in the bit vector. The actual
    /// length of the bit vector will stay unchanged, see [`BitVector::resize`] to change the actual
    /// length of the bit vector.
    ///
    /// The underlying allocator might reserve additional capacity.
    pub fn reserve(&mut self, additional: usize) {
        let new_capacity = self.length + additional;
        if Self::capacity_from_bit_len(new_capacity) > self.data.len() {
            // TODO: in place reallocation
            let mut new_data: Vec<usize> = repeat(0usize).take(Self::capacity_from_bit_len(new_capacity)).collect();
            for i in 0..self.data.len() {
                new_data[i] = self.data[i];
            }
            self.data = new_data.into_boxed_slice();
        }
    }

    /// Drop as much excess capacity as possible in the bit vector to fit the current length.
    pub fn shrink_to_fit(&mut self) {
        if Self::capacity_from_bit_len(self.length) < self.data.len() {
            // TODO: in place reallocation
            let mut new_data: Vec<usize> = repeat(0usize).take(Self::capacity_from_bit_len(self.length)).collect();
            for i in 0..new_data.len() {
                new_data[i] = self.data[i];
            }
            self.data = new_data.into_boxed_slice();
        }
    }
}

impl BitVector for BVN {
    fn zeros(length: usize) -> Self {
        let v: Vec<usize> = repeat(0).take(Self::capacity_from_bit_len(length)).collect();
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

    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertError> {
        let length = string.as_ref().chars().count();
        let offset = (Self::BIT_UNIT - length % Self::BIT_UNIT) % Self::BIT_UNIT;
        let mut data: Vec<usize> = repeat(0usize).take(Self::capacity_from_bit_len(length)).collect();

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = data.len() - 1 - (i + offset) / Self::BIT_UNIT;
            data[j] = (data[j] << 1) | match c {
                '0' => 0,
                '1' => 1,
                _ => return Err(ConvertError::InvalidFormat(i))
            };
        }
        Ok(Self {
            data: data.into_boxed_slice(),
            length
        })
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertError> {
        let length = string.as_ref().chars().count();
        let offset = (Self::NIBBLE_UNIT - length % Self::NIBBLE_UNIT) % Self::NIBBLE_UNIT;
        let mut data: Vec<usize> = repeat(0usize).take(Self::capacity_from_byte_len((length + 1) / 2)).collect();

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = data.len() - 1 - (i + offset) / Self::NIBBLE_UNIT;
            data[j] = (data[j] << 4) | match c.to_digit(16) {
                Some(d) => d as usize,
                None => return Err(ConvertError::InvalidFormat(i))
            };
        }  
        Ok(Self {
            data: data.into_boxed_slice(),
            length: length * 4
        })
    }

    fn from_bytes<B: AsRef<[u8]>>(bytes: B, endianness: Endianness) -> Result<Self, ConvertError> {
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
        Ok(Self {
            data: data.into_boxed_slice(),
            length: byte_length * 8
        })
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
        let num_bytes = (length + 7) / 8;
        let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
        reader.read_exact(&mut buf[..])?;
        let mut bv = Self::from_bytes(&buf[..], endianness).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
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

    fn copy_slice(&self, range: Range<usize>) -> Self {
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
        // TODO: optimize to do it in place
        let mut new_data: Vec<usize> = repeat(0).take(self.data.len()).collect();
        let mut old_idx = 0;
        while old_idx < self.length {
            let new_idx = (old_idx + rot) % self.length;
            let l = (Self::BIT_UNIT - new_idx % Self::BIT_UNIT)
                    .min(Self::BIT_UNIT - old_idx % Self::BIT_UNIT)
                    .min(self.length - new_idx)
                    .min(self.length - old_idx);
            new_data[new_idx / Self::BIT_UNIT] |= ((self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & Self::mask(l)) << (new_idx % Self::BIT_UNIT);
            old_idx += l;
        }
        self.data = new_data.into_boxed_slice();
    }

    fn rotr(&mut self, rot: usize) {
        // TODO: optimize to do it in place
        let mut new_data: Vec<usize> = repeat(0).take(self.data.len()).collect();
        let mut new_idx = 0;
        while new_idx < self.length {
            let old_idx = (new_idx + rot) % self.length;
            let l = (Self::BIT_UNIT - new_idx % Self::BIT_UNIT)
                    .min(Self::BIT_UNIT - old_idx % Self::BIT_UNIT)
                    .min(self.length - new_idx)
                    .min(self.length - old_idx);
            new_data[new_idx / Self::BIT_UNIT] |= ((self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & Self::mask(l)) << (new_idx % Self::BIT_UNIT);
            new_idx += l;
        }
        self.data = new_data.into_boxed_slice();
    }

    fn len(&self) -> usize {
        self.length
    }
}

impl Binary for BVN {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::with_capacity(self.length);
        for i in (0..self.length).rev() {
            match self.get(i) {
                Bit::Zero => s.push('0'),
                Bit::One => s.push('1'),
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

/// Warning: this implementation is broken for bit vector longer than 128 bits.
impl Display for BVN {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Ok(b) = BV128::try_from(self) {
            return Display::fmt(&b, f);
        }
        else {
            // TODO: waiting for div and mod operations
            todo!()
        }
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
            s.push(SEMI_NIBBLE[(self.data[i / Self::SEMI_NIBBLE_UNIT] >> ((i % Self::SEMI_NIBBLE_UNIT) * 4) & 0x7) as usize]);
        }
        if f.alternate() {
            return write!(f, "0x{}", s.as_str());
        }
        else {
            return write!(f, "{}", s.as_str());
        }
    }
}

impl PartialEq for BVN {
    fn eq(&self, other: &Self) -> bool {
        for i in 0..usize::max(self.data.len(), other.data.len()) {
            if self.data.get(i).unwrap_or(&0) != other.data.get(i).unwrap_or(&0) {
                return false;
            }
        }
        return true;
    }
}

impl Eq for BVN {}

impl Ord for BVN {
    fn cmp(&self, other: &Self) -> Ordering { 
        for i in (0..usize::max(self.data.len(), other.data.len())).rev() {
            match self.data.get(i).unwrap_or(&0).cmp(other.data.get(i).unwrap_or(&0)) {
                Ordering::Equal => continue,
                ord => return ord
            }
        }
        return Ordering::Equal;
    }
}

impl PartialOrd for BVN {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! impl_eq { ({$(($rhs:ty, $st:ty)),+}) => {
    $(
        impl PartialEq<$rhs> for BVN {
            fn eq(&self, other: &$rhs) -> bool {
                let mut it = USizeStream::new(<$st>::from(other));
                for i in 0..usize::max(self.len(), it.len()) {
                    if *self.data.get(i).unwrap_or(&0) != it.next().unwrap_or(0) {
                        return false;
                    }
                }
                return true;
            }
        }

        impl PartialEq<BVN> for $rhs {
            fn eq(&self, other: &BVN) -> bool {
                other.eq(self)
            }
        }
    )+
}}

macro_rules! impl_ord { ({$(($rhs:ty, $st:ty)),+}) => {
    $(
        impl PartialOrd<$rhs> for BVN {
            fn partial_cmp(&self, other: &$rhs) -> Option<Ordering> {
                let mut it = USizeStream::new(<$st>::from(other)).rev();
                for i in (0..usize::max(self.len(), it.len())).rev() {
                    match self.data.get(i).unwrap_or(&0).cmp(&it.next().unwrap_or(0)) {
                        Ordering::Equal => continue,
                        ord => return Some(ord)
                    }
                }
                return Some(Ordering::Equal);
            }
        }

        impl PartialOrd<BVN> for $rhs {
            fn partial_cmp(&self, other: &BVN) -> Option<Ordering> {
                other.partial_cmp(self).map(|o| o.reverse())
            }
        }
    )+
}}

impl_eq!({(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64), (BV128, u128)});
impl_ord!({(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64), (BV128, u128)});

macro_rules! impl_shifts {({$($rhs:ty),+}) => {
    $(
        impl ShlAssign<$rhs> for BVN {
            fn shl_assign(&mut self, rhs: $rhs) {
                let shift = usize::try_from(rhs).map_or(0, |s| s);
                if shift == 0 {
                    return;
                }
                let mut new_idx = self.length;
                while new_idx - shift > 0 {
                    let l = (new_idx.wrapping_sub(1) % Self::BIT_UNIT + 1)
                            .min((new_idx - shift).wrapping_sub(1) % Self::BIT_UNIT + 1);
                    new_idx -= l;
                    let old_idx = new_idx - shift;
                    let d = (self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & Self::mask(l);
                    self.data[new_idx / Self::BIT_UNIT] &= !(Self::mask(l) << (new_idx % Self::BIT_UNIT));
                    self.data[new_idx / Self::BIT_UNIT] |=  d << (new_idx % Self::BIT_UNIT);
                }
                while new_idx > 0 {
                    let l = (new_idx.wrapping_sub(1) % Self::BIT_UNIT) + 1;
                    new_idx -= l;
                    self.data[new_idx / Self::BIT_UNIT] &= !(Self::mask(l) << (new_idx % Self::BIT_UNIT));
                }
            }
        }

        impl ShlAssign<&'_ $rhs> for BVN {
            fn shl_assign(&mut self, rhs: &'_ $rhs) {
                self.shl_assign(*rhs);
            }
        }

        impl Shl<$rhs> for BVN {
            type Output = BVN;
            fn shl(mut self, rhs: $rhs) -> BVN {
                self.shl_assign(rhs);
                return self;
            }
        }

        impl Shl<&'_ $rhs> for BVN {
            type Output = BVN;
            fn shl(mut self, rhs: &'_ $rhs) -> BVN {
                self.shl_assign(rhs);
                return self;
            }
        }

        impl Shl<$rhs> for &'_ BVN {
            type Output = BVN;
            fn shl(self, rhs: $rhs) -> BVN {
                let shift = usize::try_from(rhs).map_or(0, |s| s);
                let mut new_data: Vec<usize> = repeat(0).take(BVN::capacity_from_bit_len(self.length)).collect();
                let mut new_idx = self.length;
                while new_idx - shift > 0 {
                    let l = (new_idx.wrapping_sub(1) % BVN::BIT_UNIT + 1)
                            .min((new_idx - shift).wrapping_sub(1) % BVN::BIT_UNIT + 1);
                    new_idx -= l;
                    let old_idx = new_idx - shift;
                    new_data[new_idx / BVN::BIT_UNIT] |= ((self.data[old_idx / BVN::BIT_UNIT] >> (old_idx % BVN::BIT_UNIT)) & BVN::mask(l)) << (new_idx % BVN::BIT_UNIT);
                }
                BVN {
                    data: new_data.into_boxed_slice(),
                    length: self.length
                }
            }
        }

        impl Shl<&'_ $rhs> for &'_ BVN {
            type Output = BVN;
            fn shl(self, rhs: &'_ $rhs) -> BVN {
                self.shl(*rhs)
            }
        }

        impl ShrAssign<$rhs> for BVN {
            fn shr_assign(&mut self, rhs: $rhs) {
                let shift = usize::try_from(rhs).map_or(0, |s| s);
                if shift == 0 {
                    return;
                }
                let mut new_idx = 0;
                while new_idx + shift < self.length {
                    let old_idx = new_idx + shift;
                    let l = (Self::BIT_UNIT - new_idx % Self::BIT_UNIT)
                            .min(Self::BIT_UNIT - old_idx % Self::BIT_UNIT);
                    let d = (self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & Self::mask(l);
                    self.data[new_idx / Self::BIT_UNIT] &= !(Self::mask(l) << (new_idx % Self::BIT_UNIT));
                    self.data[new_idx / Self::BIT_UNIT] |= d << (new_idx % Self::BIT_UNIT);
                    new_idx += l;
                }
                while new_idx < self.length {
                    let l = Self::BIT_UNIT - new_idx % Self::BIT_UNIT;
                    self.data[new_idx / Self::BIT_UNIT] &= !(Self::mask(l) << (new_idx % Self::BIT_UNIT));
                    new_idx += l;
                }
            }
        }

        impl ShrAssign<&'_ $rhs> for BVN {
            fn shr_assign(&mut self, rhs: &'_ $rhs) {
                self.shr_assign(*rhs);
            }
        }

        impl Shr<$rhs> for BVN {
            type Output = BVN;
            fn shr(mut self, rhs: $rhs) -> BVN {
                self.shr_assign(rhs);
                return self;
            }
        }

        impl Shr<&'_ $rhs> for BVN {
            type Output = BVN;
            fn shr(mut self, rhs: &'_ $rhs) -> BVN {
                self.shr_assign(rhs);
                return self;
            }
        }

        impl Shr<$rhs> for &'_ BVN {
            type Output = BVN;
            fn shr(self, rhs: $rhs) -> BVN {
                let shift = usize::try_from(rhs).map_or(0, |s| s);
                let mut new_data: Vec<usize> = repeat(0).take(BVN::capacity_from_bit_len(self.length)).collect();
                let mut new_idx = 0;
                while new_idx + shift < self.length {
                    let old_idx = new_idx + shift;
                    let l = (BVN::BIT_UNIT - new_idx % BVN::BIT_UNIT)
                            .min(BVN::BIT_UNIT - old_idx % BVN::BIT_UNIT);
                    new_data[new_idx / BVN::BIT_UNIT] |= ((self.data[old_idx / BVN::BIT_UNIT] >> (old_idx % BVN::BIT_UNIT)) & BVN::mask(l)) << (new_idx % BVN::BIT_UNIT);
                    new_idx += l;
                }
                BVN {
                    data: new_data.into_boxed_slice(),
                    length: self.length
                }
            }
        }

        impl Shr<&'_ $rhs> for &'_ BVN {
            type Output = BVN;
            fn shr(self, rhs: &'_ $rhs) -> BVN {
                self.shr(*rhs)
            }
        }
    )+
}}

impl_shifts!({u8, u16, u32, u64, u128, usize});

impl Not for BVN {
    type Output = BVN;
    fn not(mut self) -> Self::Output {
        for i in 0..Self::capacity_from_bit_len(self.length) {
            self.data[i] = !self.data[i];
        }
        if let Some(l) = self.data.get_mut(self.length / Self::BIT_UNIT) {
            *l &= Self::mask(self.length % Self::BIT_UNIT);
        }
        return self;
    }
}

impl Not for &'_ BVN {
    type Output = BVN;
    fn not(self) -> Self::Output {
        let mut new_data: Vec<usize> = self.data[0..BVN::capacity_from_bit_len(self.length)]
                                       .iter().map(|d| !d).collect();
        if let Some(l) = new_data.get_mut(self.length / BVN::BIT_UNIT) {
            *l &= BVN::mask(self.length % BVN::BIT_UNIT);
        }
        BVN {
            data: new_data.into_boxed_slice(),
            length: self.length
        }
    }
}


macro_rules! impl_froms {({$(($rhs:ty, $st:ty)),+}) => {
    $(
        impl From<$st> for BVN {
            fn from(st: $st) -> Self {
                let it = USizeStream::new(st);
                BVN {
                    length: it.bit_length(),
                    data: it.collect(),
                }
            }
        }

        impl From<&'_ $rhs> for BVN {
            fn from(rhs: &'_ $rhs) -> BVN {
                let it = USizeStream::new(<$st>::from(rhs));
                BVN {
                    length: rhs.len(),
                    data: it.collect(),
                }
            }
        }

        impl From<$rhs> for BVN {
            fn from(rhs: $rhs) -> BVN {
                BVN::from(&rhs)
            }
        }

        impl TryFrom<&'_ BVN> for $st {
            type Error = &'static str;
            #[allow(arithmetic_overflow)]
            fn try_from(bvn: &'_ BVN) -> Result<Self, Self::Error> {
                if bvn.length > size_of::<$st>() * 8 {
                    return Err("BVN is too large to convert into this type");
                }
                else {
                    let mut r: $st = 0;
                    for i in (0..BVN::capacity_from_bit_len(bvn.length)).rev() {
                        r = r.checked_shl(BVN::BIT_UNIT as u32).unwrap_or(0) | bvn.data[i] as $st;
                    }
                    return Ok(r);
                }
            }
        }

        impl TryFrom<BVN> for $st {
            type Error = &'static str;
            fn try_from(bvn: BVN) -> Result<Self, Self::Error> {
                <$st>::try_from(&bvn)
            }
        }

        impl TryFrom<&'_ BVN> for $rhs {
            type Error = &'static str;
            fn try_from(bvn: &'_ BVN) -> Result<Self, Self::Error> {
                let mut r = <$rhs>::from(<$st>::try_from(bvn)?);
                r.resize(bvn.length, Bit::Zero);
                Ok(r)
            }
        }

        impl TryFrom<BVN> for $rhs {
            type Error = &'static str;
            fn try_from(bvn: BVN) -> Result<Self, Self::Error> {
                <$rhs>::try_from(&bvn)
            }
        }
    )+
}}

impl_froms!({(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64), (BV128, u128)});


macro_rules! impl_binop_assign { ($trait:ident, $method:ident, {$(($rhs:ty, $st:ty)),+}) => {
    impl $trait<&'_ BVN> for BVN {
        fn $method(&mut self, rhs: &'_ BVN) {
            if rhs.length > self.length {
                self.resize(rhs.length, Bit::Zero);
            }
            for i in 0..Self::capacity_from_bit_len(rhs.length) {
                self.data[i].$method(rhs.data[i]);
            }
            for i in Self::capacity_from_bit_len(rhs.length)..Self::capacity_from_bit_len(self.length) {
                self.data[i].$method(0);
            }
        }
    }

    impl $trait<BVN> for BVN {
        fn $method(&mut self, rhs: BVN) {
            self.$method(&rhs);
        }
    }

    $(
        impl $trait<&'_ $rhs> for BVN {
            fn $method(&mut self, rhs: &'_ $rhs) {
                if rhs.len() > self.length {
                    self.resize(rhs.len(), Bit::Zero);
                }
                let mut it = USizeStream::new(<$st>::from(*rhs));
                for i in 0..Self::capacity_from_bit_len(rhs.len()) {
                    self.data[i].$method(it.next().unwrap());
                }
                for i in Self::capacity_from_bit_len(rhs.len())..Self::capacity_from_bit_len(self.length) {
                    self.data[i].$method(0);
                }
            }
        }

        impl $trait<$rhs> for BVN {
            fn $method(&mut self, rhs: $rhs) {
                self.$method(&rhs);
            }
        }
    )+
}}

impl_binop_assign!(BitAndAssign, bitand_assign, {(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64), (BV128, u128)});
impl_binop_assign!(BitOrAssign, bitor_assign, {(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64), (BV128, u128)});
impl_binop_assign!(BitXorAssign, bitxor_assign, {(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64), (BV128, u128)});

macro_rules! impl_addsub_assign { ($trait:ident, $method:ident, $overflowing_method:ident, {$(($rhs:ty, $st:ty)),+}) => {
    impl $trait<&'_ BVN> for BVN {
        fn $method(&mut self, rhs: &'_ BVN) {
            if rhs.length > self.length {
                self.resize(rhs.length, Bit::Zero);
            }
            let mut carry = 0;
            for i in 0..Self::capacity_from_bit_len(rhs.length) {
                let (d1, c1) = self.data[i].$overflowing_method(carry);
                let (d2, c2) = d1.$overflowing_method(rhs.data[i]);
                self.data[i] = d2;
                carry = (c1 | c2) as usize;
            }
            for i in Self::capacity_from_bit_len(rhs.length)..Self::capacity_from_bit_len(self.length) {
                let (d, c) = self.data[i].$overflowing_method(carry);
                self.data[i] = d;
                carry = c as usize;
            }
            if let Some(l) = self.data.get_mut(self.length / BVN::BIT_UNIT) {
                *l &= Self::mask(self.length % BVN::BIT_UNIT);
            }
        }
    }

    impl $trait<BVN> for BVN {
        fn $method(&mut self, rhs: BVN) {
            self.$method(&rhs);
        }
    }

    $(
        impl $trait<&'_ $rhs> for BVN {
            fn $method(&mut self, rhs: &'_ $rhs) {
                if rhs.len() > self.length {
                    self.resize(rhs.len(), Bit::Zero);
                }
                let mut carry = 0;
                let mut it = USizeStream::new(<$st>::from(*rhs));
                for i in 0..Self::capacity_from_bit_len(rhs.len()) {
                    let (d1, c1) = self.data[i].$overflowing_method(carry);
                    let (d2, c2) = d1.$overflowing_method(it.next().unwrap());
                    self.data[i] = d2;
                    carry = (c1 | c2) as usize;
                }
                for i in Self::capacity_from_bit_len(rhs.len())..Self::capacity_from_bit_len(self.length) {
                    let (d, c) = self.data[i].$overflowing_method(carry);
                    self.data[i] = d;
                    carry = c as usize;
                }
                if let Some(l) = self.data.get_mut(self.length / BVN::BIT_UNIT) {
                    *l &= Self::mask(self.length % BVN::BIT_UNIT);
                }
            }
        }

        impl $trait<$rhs> for BVN {
            fn $method(&mut self, rhs: $rhs) {
                self.$method(&rhs);
            }
        }
    )+
}}

impl_addsub_assign!(AddAssign, add_assign, overflowing_add, {(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64), (BV128, u128)});
impl_addsub_assign!(SubAssign, sub_assign, overflowing_sub, {(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64), (BV128, u128)});

macro_rules! impl_op { ($trait:ident, $method:ident, $assign_method:ident, {$($rhs:ty),+}) => {
    impl $trait<BVN> for BVN {
        type Output = BVN;
        fn $method(mut self, rhs: BVN) -> BVN {
            self.$assign_method(rhs);
            return self;
        }
    }

    impl $trait<&'_ BVN> for BVN {
        type Output = BVN;
        fn $method(mut self, rhs: &'_ BVN) -> BVN {
            self.$assign_method(rhs);
            return self;
        }
    }

    impl $trait<BVN> for &'_ BVN {
        type Output = BVN;
        fn $method(self, rhs: BVN) -> BVN {
            return self.clone().$method(rhs);
        }
    }

    impl $trait<&'_ BVN> for &'_ BVN {
        type Output = BVN;
        fn $method(self, rhs: &'_ BVN) -> BVN {
            return self.clone().$method(rhs);
        }
    }

    $(
        impl $trait<$rhs> for BVN {
            type Output = BVN;
            fn $method(mut self, rhs: $rhs) -> BVN {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl $trait<&'_ $rhs> for BVN {
            type Output = BVN;
            fn $method(mut self, rhs: &'_ $rhs) -> BVN {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl $trait<$rhs> for &'_ BVN {
            type Output = BVN;
            fn $method(self, rhs: $rhs) -> BVN {
                return self.clone().$method(rhs);
            }
        }

        impl $trait<&'_ $rhs> for &'_ BVN {
            type Output = BVN;
            fn $method(self, rhs: &'_ $rhs) -> BVN {
                return self.clone().$method(rhs);
            }
        }
    )+
}}

impl_op!(BitAnd, bitand, bitand_assign, {BV8, BV16, BV32, BV64, BV128});
impl_op!(BitOr, bitor, bitor_assign, {BV8, BV16, BV32, BV64, BV128});
impl_op!(BitXor, bitxor, bitxor_assign, {BV8, BV16, BV32, BV64, BV128});
impl_op!(Add, add, add_assign, {BV8, BV16, BV32, BV64, BV128});
impl_op!(Sub, sub, sub_assign, {BV8, BV16, BV32, BV64, BV128});