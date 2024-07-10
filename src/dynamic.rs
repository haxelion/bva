//! This module contains a dynamic capacity bit vector implementation using a dynamically allocated
//! integer array as storage.
//!
//! As the capacity is dynamic, performing operations exceeding the current capacity will result in
//! a reallocation of the internal array.

use std::cmp::Ordering;
use std::fmt;
use std::io::{Read, Write};
use std::iter::repeat;
use std::mem::size_of;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Range, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::auto::BV;
use crate::fixed::BVF;
use crate::iter::BitIterator;
use crate::utils::{IArray, IArrayMut, Integer, StaticCast};
use crate::{Bit, BitVector, ConvertionError, Endianness};

// ------------------------------------------------------------------------------------------------
// Bit Vector Dynamic allocation implementation
// ------------------------------------------------------------------------------------------------

/// A bit vector with dynamic capacity.
#[derive(Clone, Debug)]
pub struct BVD {
    data: Box<[u64]>,
    length: usize,
}

impl BVD {
    const BYTE_UNIT: usize = size_of::<u64>();
    const NIBBLE_UNIT: usize = size_of::<u64>() * 2;
    const BIT_UNIT: usize = u64::BITS as usize;

    fn capacity_from_byte_len(byte_length: usize) -> usize {
        (byte_length + size_of::<u64>() - 1) / size_of::<u64>()
    }

    fn capacity_from_bit_len(bit_length: usize) -> usize {
        Self::capacity_from_byte_len((bit_length + 7) / 8)
    }

    fn mask(length: usize) -> u64 {
        u64::MAX
            .checked_shr((Self::BIT_UNIT - length) as u32)
            .unwrap_or(0)
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
            let mut new_data: Vec<u64> = repeat(0)
                .take(Self::capacity_from_bit_len(new_capacity))
                .collect();
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
            let mut new_data: Vec<u64> = repeat(0)
                .take(Self::capacity_from_bit_len(self.length))
                .collect();
            for i in 0..new_data.len() {
                new_data[i] = self.data[i];
            }
            self.data = new_data.into_boxed_slice();
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BVD - Integer Array traits
// ------------------------------------------------------------------------------------------------

impl IArray for BVD {
    type I = u64;

    fn int_len<J: Integer>(&self) -> usize
    where
        u64: StaticCast<J>,
    {
        (self.len() + size_of::<J>() * 8 - 1) / (size_of::<J>() * 8)
    }

    fn get_int<J: Integer>(&self, idx: usize) -> Option<J>
    where
        u64: StaticCast<J>,
    {
        if idx < IArray::int_len::<J>(self) {
            IArray::get_int::<J>(self.data.as_ref(), idx)
        } else {
            None
        }
    }
}

impl IArrayMut for BVD {
    type I = u64;

    fn set_int<J: Integer>(&mut self, idx: usize, v: J) -> Option<J>
    where
        u64: StaticCast<J>,
    {
        if idx < IArray::int_len::<J>(self) {
            IArrayMut::set_int::<J>(self.data.as_mut(), idx, v)
        } else {
            None
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BVD - Bit Vector core trait
// ------------------------------------------------------------------------------------------------

impl BitVector for BVD {
    fn with_capacity(capacity: usize) -> Self {
        let data: Vec<u64> = repeat(0u64)
            .take(Self::capacity_from_bit_len(capacity))
            .collect();
        BVD {
            data: data.into_boxed_slice(),
            length: 0,
        }
    }

    fn zeros(length: usize) -> Self {
        let v: Vec<u64> = repeat(0)
            .take(Self::capacity_from_bit_len(length))
            .collect();
        BVD {
            data: v.into_boxed_slice(),
            length,
        }
    }

    fn ones(length: usize) -> Self {
        let mut v: Vec<u64> = repeat(u64::MAX)
            .take(Self::capacity_from_bit_len(length))
            .collect();
        if let Some(l) = v.last_mut() {
            *l &= Self::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }

        BVD {
            data: v.into_boxed_slice(),
            length,
        }
    }

    fn capacity(&self) -> usize {
        self.data.len() * Self::BIT_UNIT
    }

    fn len(&self) -> usize {
        self.length
    }

    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError> {
        let length = string.as_ref().chars().count();
        let offset = (Self::BIT_UNIT - length % Self::BIT_UNIT) % Self::BIT_UNIT;
        let mut data: Vec<u64> = repeat(0)
            .take(Self::capacity_from_bit_len(length))
            .collect();

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = data.len() - 1 - (i + offset) / Self::BIT_UNIT;
            data[j] = (data[j] << 1)
                | match c {
                    '0' => 0,
                    '1' => 1,
                    _ => return Err(ConvertionError::InvalidFormat(i)),
                };
        }
        Ok(Self {
            data: data.into_boxed_slice(),
            length,
        })
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError> {
        let length = string.as_ref().chars().count();
        let offset = (Self::NIBBLE_UNIT - length % Self::NIBBLE_UNIT) % Self::NIBBLE_UNIT;
        let mut data: Vec<u64> = repeat(0)
            .take(Self::capacity_from_byte_len((length + 1) / 2))
            .collect();

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = data.len() - 1 - (i + offset) / Self::NIBBLE_UNIT;
            data[j] = (data[j] << 4)
                | match c.to_digit(16) {
                    Some(d) => d as u64,
                    None => return Err(ConvertionError::InvalidFormat(i)),
                };
        }
        Ok(Self {
            data: data.into_boxed_slice(),
            length: length * 4,
        })
    }

    fn from_bytes<B: AsRef<[u8]>>(
        bytes: B,
        endianness: Endianness,
    ) -> Result<Self, ConvertionError> {
        let byte_length = bytes.as_ref().len();
        let mut data: Vec<u64> = repeat(0)
            .take(Self::capacity_from_byte_len(byte_length))
            .collect();
        match endianness {
            Endianness::LE => {
                let offset = (Self::BYTE_UNIT - byte_length % Self::BYTE_UNIT) % Self::BYTE_UNIT;
                for (i, b) in bytes.as_ref().iter().rev().enumerate() {
                    let j = data.len() - 1 - (i + offset) / Self::BYTE_UNIT;
                    data[j] = (data[j] << 8) | *b as u64;
                }
            }
            Endianness::BE => {
                let offset = (Self::BYTE_UNIT - byte_length % Self::BYTE_UNIT) % Self::BYTE_UNIT;
                for (i, b) in bytes.as_ref().iter().enumerate() {
                    let j = data.len() - 1 - (i + offset) / Self::BYTE_UNIT;
                    data[j] = (data[j] << 8) | *b as u64;
                }
            }
        }
        Ok(Self {
            data: data.into_boxed_slice(),
            length: byte_length * 8,
        })
    }

    fn to_vec(&self, endianness: Endianness) -> Vec<u8> {
        let num_bytes = (self.length + 7) / 8;
        let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
        match endianness {
            Endianness::LE => {
                for i in 0..num_bytes {
                    buf[i] = (self.data[i / Self::BYTE_UNIT] >> ((i % Self::BYTE_UNIT) * 8) & 0xff)
                        as u8;
                }
            }
            Endianness::BE => {
                for i in 0..num_bytes {
                    buf[num_bytes - i - 1] = (self.data[i / Self::BYTE_UNIT]
                        >> ((i % Self::BYTE_UNIT) * 8)
                        & 0xff) as u8;
                }
            }
        }
        buf
    }

    fn read<R: Read>(
        reader: &mut R,
        length: usize,
        endianness: Endianness,
    ) -> std::io::Result<Self> {
        let num_bytes = (length + 7) / 8;
        let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
        reader.read_exact(&mut buf[..])?;
        let mut bv = Self::from_bytes(&buf[..], endianness)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        if let Some(l) = bv.data.last_mut() {
            *l &= Self::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }
        bv.length = length;
        Ok(bv)
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
        self.data[index / Self::BIT_UNIT] = (self.data[index / Self::BIT_UNIT]
            & !(1 << (index % Self::BIT_UNIT)))
            | ((bit as u64) << (index % Self::BIT_UNIT));
    }

    fn copy_range(&self, range: Range<usize>) -> Self {
        debug_assert!(range.start <= self.len() && range.end <= self.len());
        let length = range.end - usize::min(range.start, range.end);
        let mut data: Vec<u64> = repeat(0)
            .take(Self::capacity_from_bit_len(length))
            .collect();
        let offset = range.start / Self::BIT_UNIT;
        let slide = range.start % Self::BIT_UNIT;

        for i in 0..data.len() {
            data[i] = (self.data[i + offset] >> slide)
                | self
                    .data
                    .get(i + offset + 1)
                    .unwrap_or(&0)
                    .checked_shl((Self::BIT_UNIT - slide) as u32)
                    .unwrap_or(0);
        }
        if let Some(l) = data.last_mut() {
            *l &= Self::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }

        BVD {
            data: data.into_boxed_slice(),
            length,
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
        self.set(self.length - 1, Bit::Zero);
        self.length -= 1;
        Some(bit)
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
        } else if new_length > self.length {
            let sign_pattern = match bit {
                Bit::Zero => u64::MIN,
                Bit::One => u64::MAX,
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

    fn append<B: BitVector>(&mut self, suffix: &B) {
        self.reserve(self.length + suffix.len());
        // TODO: can be optimized with a shift and data copy via IArray.
        // The IArray trait would need rework to support this.
        for b in suffix.iter() {
            self.push(b);
        }
    }

    fn prepend<B: BitVector>(&mut self, prefix: &B) {
        self.resize(prefix.len() + self.length, Bit::Zero);
        *self <<= prefix.len();
        // TODO: can be optimized with data copy via IArray.
        // The IArray trait would need rework to support this.
        for (i, b) in prefix.iter().enumerate() {
            self.set(i, b);
        }
    }

    fn shl_in(&mut self, bit: Bit) -> Bit {
        let mut carry = bit;
        for i in 0..(self.length / Self::BIT_UNIT) {
            let b = self.data[i] >> (Self::BIT_UNIT - 1) & 1;
            self.data[i] = self.data[i] << 1 | carry as u64;
            carry = b.into();
        }
        if self.length % Self::BIT_UNIT != 0 {
            let i = self.length / Self::BIT_UNIT;
            let b = self.data[i] >> (self.length % Self::BIT_UNIT - 1) & 1;
            self.data[i] =
                (self.data[i] << 1 | carry as u64) & Self::mask(self.length % Self::BIT_UNIT);
            carry = b.into();
        }
        carry
    }

    fn shr_in(&mut self, bit: Bit) -> Bit {
        let mut carry = bit;
        if self.length % Self::BIT_UNIT != 0 {
            let i = self.length / Self::BIT_UNIT;
            let b = self.data[i] & 1;
            self.data[i] = self.data[i] >> 1 | (carry as u64) << (self.length % Self::BIT_UNIT - 1);
            carry = b.into();
        }
        for i in (0..(self.length / Self::BIT_UNIT)).rev() {
            let b = self.data[i] & 1;
            self.data[i] = self.data[i] >> 1 | (carry as u64) << (Self::BIT_UNIT - 1);
            carry = b.into();
        }
        carry
    }

    fn rotl(&mut self, rot: usize) {
        // TODO: optimize to do it in place
        let mut new_data: Vec<u64> = repeat(0).take(self.data.len()).collect();
        let mut old_idx = 0;
        while old_idx < self.length {
            let new_idx = (old_idx + rot) % self.length;
            let l = (Self::BIT_UNIT - new_idx % Self::BIT_UNIT)
                .min(Self::BIT_UNIT - old_idx % Self::BIT_UNIT)
                .min(self.length - new_idx)
                .min(self.length - old_idx);
            new_data[new_idx / Self::BIT_UNIT] |= ((self.data[old_idx / Self::BIT_UNIT]
                >> (old_idx % Self::BIT_UNIT))
                & Self::mask(l))
                << (new_idx % Self::BIT_UNIT);
            old_idx += l;
        }
        self.data = new_data.into_boxed_slice();
    }

    fn rotr(&mut self, rot: usize) {
        // TODO: optimize to do it in place
        let mut new_data: Vec<u64> = repeat(0).take(self.data.len()).collect();
        let mut new_idx = 0;
        while new_idx < self.length {
            let old_idx = (new_idx + rot) % self.length;
            let l = (Self::BIT_UNIT - new_idx % Self::BIT_UNIT)
                .min(Self::BIT_UNIT - old_idx % Self::BIT_UNIT)
                .min(self.length - new_idx)
                .min(self.length - old_idx);
            new_data[new_idx / Self::BIT_UNIT] |= ((self.data[old_idx / Self::BIT_UNIT]
                >> (old_idx % Self::BIT_UNIT))
                & Self::mask(l))
                << (new_idx % Self::BIT_UNIT);
            new_idx += l;
        }
        self.data = new_data.into_boxed_slice();
    }

    fn leading_zeros(&self) -> usize {
        let mut count = 0;
        let mut i = Self::capacity_from_bit_len(self.length);
        if i > 0 {
            let lastbit = (self.length - 1) % Self::BIT_UNIT + 1;
            let mut v = self.data[i - 1] & Self::mask(lastbit);
            count += Integer::leading_zeros(&v) - (Self::BIT_UNIT - lastbit);
            i -= 1;
            while v == 0 && i > 0 {
                v = self.data[i - 1];
                count += Integer::leading_zeros(&v);
                i -= 1;
            }
        }
        count
    }

    fn leading_ones(&self) -> usize {
        let mut count = 0;
        let mut i = Self::capacity_from_bit_len(self.length);
        if i > 0 {
            let lastbit = (self.length - 1) % Self::BIT_UNIT + 1;
            let mut v = self.data[i - 1] | !Self::mask(lastbit);
            count += Integer::leading_ones(&v) - (Self::BIT_UNIT - lastbit);
            i -= 1;
            while v == u64::MAX && i > 0 {
                v = self.data[i - 1];
                count += Integer::leading_ones(&v);
                i -= 1;
            }
        }
        count
    }

    fn trailing_zeros(&self) -> usize {
        let mut count = 0;
        let mut i = 0;
        if i < Self::capacity_from_bit_len(self.length) {
            let mut v = 0;
            while v == 0 && i < Self::capacity_from_bit_len(self.length) - 1 {
                v = self.data[i];
                count += Integer::trailing_zeros(&v);
                i += 1;
            }
            if v == 0 {
                let lastbit = (self.length - 1) % Self::BIT_UNIT + 1;
                count += usize::min(Integer::trailing_zeros(&self.data[i]), lastbit);
            }
        }
        count
    }

    fn trailing_ones(&self) -> usize {
        let mut count = 0;
        let mut i = 0;
        if i < Self::capacity_from_bit_len(self.length) {
            let mut v = u64::MAX;
            while v == u64::MAX && i < Self::capacity_from_bit_len(self.length) - 1 {
                v = self.data[i];
                count += Integer::trailing_ones(&v);
                i += 1;
            }
            if v == u64::MAX {
                let lastbit = (self.length - 1) % Self::BIT_UNIT + 1;
                count += usize::min(Integer::trailing_ones(&self.data[i]), lastbit);
            }
        }
        count
    }

    fn is_zero(&self) -> bool {
        self.data[0..Self::capacity_from_bit_len(self.length)]
            .iter()
            .all(|&x| x == 0)
    }

    fn div_rem<B: BitVector>(&self, divisor: &B) -> (Self, Self)
    where
        Self: for<'a> TryFrom<&'a B, Error: std::fmt::Debug>,
    {
        assert!(!divisor.is_zero(), "Division by zero");
        let mut quotient = BVD::zeros(self.length);
        let mut rem = self.clone();
        if divisor.significant_bits() > self.significant_bits() {
            return (quotient, rem);
        }

        let shift = self.significant_bits() - divisor.significant_bits();
        let mut divisor: BVD = divisor.try_into().expect("should never fail");
        divisor.resize(self.length, Bit::Zero);
        divisor <<= shift;

        for i in (0..shift + 1).rev() {
            if rem >= divisor {
                rem -= &divisor;
                quotient.set(i, Bit::One);
            }
            divisor >>= 1u32;
        }

        (quotient, rem)
    }

    fn iter(&self) -> BitIterator<'_, Self> {
        self.into_iter()
    }
}

// ------------------------------------------------------------------------------------------------
// BVD - Bit iterator traits
// ------------------------------------------------------------------------------------------------

impl<'a> IntoIterator for &'a BVD {
    type Item = Bit;
    type IntoIter = BitIterator<'a, BVD>;

    fn into_iter(self) -> Self::IntoIter {
        BitIterator::new(self)
    }
}

impl FromIterator<Bit> for BVD {
    fn from_iter<T: IntoIterator<Item = Bit>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut bv = BVD::with_capacity(iter.size_hint().0);
        iter.for_each(|b| bv.push(b));
        bv
    }
}

impl Extend<Bit> for BVD {
    fn extend<T: IntoIterator<Item = Bit>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        iter.for_each(|b| self.push(b));
    }
}

// ------------------------------------------------------------------------------------------------
// BVD - Formatting traits
// ------------------------------------------------------------------------------------------------

impl fmt::Binary for BVD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut i = self.length;

        // Skip trailling 0
        while i > 0 && self.get(i - 1) == Bit::Zero {
            i -= 1;
        }

        let mut s = String::with_capacity(self.length);
        while i > 0 {
            match self.get(i - 1) {
                Bit::Zero => s.push('0'),
                Bit::One => s.push('1'),
            }
            i -= 1;
        }
        if s.is_empty() {
            s.push('0');
        }

        f.pad_integral(true, "0b", &s)
    }
}

impl fmt::Display for BVD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let base = Self::from(10u8);
        let mut s = Vec::<char>::new();
        let mut quotient = self.clone();
        let mut remainder;

        while !quotient.is_zero() {
            (quotient, remainder) = quotient.div_rem(&base);
            // Remainder of division by 10 will be a single digit
            s.push(char::from_digit(u32::try_from(&remainder).unwrap(), 10).unwrap());
        }
        if s.is_empty() {
            s.push('0');
        }

        f.pad_integral(true, "", s.iter().rev().collect::<String>().as_str())
    }
}

impl fmt::Octal for BVD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const SEMI_NIBBLE: [char; 8] = ['0', '1', '2', '3', '4', '5', '6', '7'];
        let length = (self.length + 2) / 3;
        let mut s = Vec::<char>::with_capacity(length);
        let mut it = self.iter();
        let mut last_nz = 0;

        while let Some(b0) = it.next() {
            let b1 = it.next().unwrap_or(Bit::Zero);
            let b2 = it.next().unwrap_or(Bit::Zero);
            let octet = (b2 as u8) << 2 | (b1 as u8) << 1 | b0 as u8;
            if octet != 0 {
                last_nz = s.len();
            }
            s.push(SEMI_NIBBLE[octet as usize]);
        }
        if s.is_empty() {
            s.push('0');
        }
        s.truncate(last_nz + 1);

        f.pad_integral(true, "0o", s.iter().rev().collect::<String>().as_str())
    }
}

impl fmt::LowerHex for BVD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const NIBBLE: [char; 16] = [
            '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
        ];
        let mut i = (self.length + 3) / 4;

        // Skip trailling 0
        while i > 0
            && StaticCast::<u8>::cast_to(
                self.data[(i - 1) / Self::NIBBLE_UNIT] >> (((i - 1) % Self::NIBBLE_UNIT) * 4),
            ) & 0xf
                == 0
        {
            i -= 1;
        }

        let mut s = String::with_capacity(i);
        while i > 0 {
            let nibble = StaticCast::<u8>::cast_to(
                self.data[(i - 1) / Self::NIBBLE_UNIT] >> (((i - 1) % Self::NIBBLE_UNIT) * 4),
            ) & 0xf;
            s.push(NIBBLE[nibble as usize]);
            i -= 1;
        }
        if s.is_empty() {
            s.push('0');
        }

        f.pad_integral(true, "0x", &s)
    }
}

impl fmt::UpperHex for BVD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const NIBBLE: [char; 16] = [
            '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F',
        ];
        let mut i = (self.length + 3) / 4;
        let mut s = String::with_capacity(i);

        while i > 0
            && StaticCast::<u8>::cast_to(
                self.data[(i - 1) / Self::NIBBLE_UNIT] >> (((i - 1) % Self::NIBBLE_UNIT) * 4),
            ) & 0xf
                == 0
        {
            i -= 1;
        }
        while i > 0 {
            let nibble = StaticCast::<u8>::cast_to(
                self.data[(i - 1) / Self::NIBBLE_UNIT] >> (((i - 1) % Self::NIBBLE_UNIT) * 4),
            ) & 0xf;
            s.push(NIBBLE[nibble as usize]);
            i -= 1;
        }
        if s.is_empty() {
            s.push('0');
        }

        f.pad_integral(true, "0x", &s)
    }
}

// ------------------------------------------------------------------------------------------------
// BVD - Comparison traits
// ------------------------------------------------------------------------------------------------

impl PartialEq for BVD {
    fn eq(&self, other: &Self) -> bool {
        for i in 0..usize::max(self.data.len(), other.data.len()) {
            if self.data.get(i).unwrap_or(&0) != other.data.get(i).unwrap_or(&0) {
                return false;
            }
        }
        true
    }
}

impl<I: Integer, const N: usize> PartialEq<BVF<I, N>> for BVD {
    fn eq(&self, other: &BVF<I, N>) -> bool {
        for i in 0..usize::max(self.len(), IArray::int_len::<u64>(other)) {
            if *self.data.get(i).unwrap_or(&0) != IArray::get_int(other, i).unwrap_or(0) {
                return false;
            }
        }
        true
    }
}

impl PartialEq<BV> for BVD {
    fn eq(&self, other: &BV) -> bool {
        other.eq(self)
    }
}

impl Eq for BVD {}

impl PartialOrd for BVD {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: Integer, const N: usize> PartialOrd<BVF<I, N>> for BVD {
    fn partial_cmp(&self, other: &BVF<I, N>) -> Option<Ordering> {
        for i in (0..usize::max(self.len(), IArray::int_len::<u64>(other))).rev() {
            match self
                .data
                .get(i)
                .unwrap_or(&0)
                .cmp(&IArray::get_int(other, i).unwrap_or(0))
            {
                Ordering::Equal => continue,
                ord => return Some(ord),
            }
        }
        Some(Ordering::Equal)
    }
}

impl PartialOrd<BV> for BVD {
    fn partial_cmp(&self, other: &BV) -> Option<Ordering> {
        other.partial_cmp(self).map(|o| o.reverse())
    }
}

impl Ord for BVD {
    fn cmp(&self, other: &Self) -> Ordering {
        for i in (0..usize::max(self.data.len(), other.data.len())).rev() {
            match self
                .data
                .get(i)
                .unwrap_or(&0)
                .cmp(other.data.get(i).unwrap_or(&0))
            {
                Ordering::Equal => continue,
                ord => return ord,
            }
        }
        Ordering::Equal
    }
}

// ------------------------------------------------------------------------------------------------
// BVD - Conversion traits
// ------------------------------------------------------------------------------------------------

impl From<&BVD> for BVD {
    fn from(bvd: &BVD) -> Self {
        BVD {
            length: bvd.len(),
            data: bvd.data.clone(),
        }
    }
}

macro_rules! impl_from_ints {($($st:ty),+) => {
    $(
        impl From<$st> for BVD {
            fn from(st: $st) -> Self {
                let array = [st];
                BVD {
                    length: <$st>::BITS as usize,
                    data: (0..IArray::int_len::<u64>(array.as_ref())).map(|i| IArray::get_int(array.as_ref(), i).unwrap()).collect(),
                }
            }
        }

        impl TryFrom<&BVD> for $st {
            type Error = ConvertionError;
            fn try_from(bvd: &BVD) -> Result<Self, Self::Error> {
                if bvd.significant_bits() > <$st>::BITS as usize {
                    return Err(ConvertionError::NotEnoughCapacity);
                }
                else {
                    let mut r: $st = 0;
                    for i in (0..BVD::capacity_from_bit_len(bvd.length)).rev() {
                        r = r.checked_shl(BVD::BIT_UNIT as u32).unwrap_or(0) | bvd.data[i] as $st;
                    }
                    return Ok(r);
                }
            }
        }

        impl TryFrom<BVD> for $st {
            type Error = ConvertionError;
            fn try_from(bvd: BVD) -> Result<Self, Self::Error> {
                <$st>::try_from(&bvd)
            }
        }
    )+
}}

impl_from_ints!(u8, u16, u32, u64, u128, usize);

impl<I: Integer, const N: usize> From<&BVF<I, N>> for BVD {
    fn from(rhs: &BVF<I, N>) -> BVD {
        BVD {
            length: rhs.len(),
            data: (0..IArray::int_len::<u64>(rhs))
                .map(|i| IArray::get_int(rhs, i).unwrap())
                .collect(),
        }
    }
}

impl<I: Integer, const N: usize> From<BVF<I, N>> for BVD {
    fn from(rhs: BVF<I, N>) -> BVD {
        BVD::from(&rhs)
    }
}

impl From<&'_ BV> for BVD {
    fn from(bv: &'_ BV) -> Self {
        match bv {
            BV::Fixed(b) => BVD::from(b),
            BV::Dynamic(b) => b.clone(),
        }
    }
}

impl From<BV> for BVD {
    fn from(bv: BV) -> Self {
        match bv {
            BV::Fixed(b) => BVD::from(b),
            BV::Dynamic(b) => b,
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BVD - Unary operator & shifts
// ------------------------------------------------------------------------------------------------

impl Not for BVD {
    type Output = BVD;
    fn not(mut self) -> Self::Output {
        for i in 0..Self::capacity_from_bit_len(self.length) {
            self.data[i] = !self.data[i];
        }
        if let Some(l) = self.data.get_mut(self.length / Self::BIT_UNIT) {
            *l &= Self::mask(self.length % Self::BIT_UNIT);
        }
        self
    }
}

impl Not for &BVD {
    type Output = BVD;
    fn not(self) -> Self::Output {
        let mut new_data: Vec<u64> = self.data[0..BVD::capacity_from_bit_len(self.length)]
            .iter()
            .map(|d| !d)
            .collect();
        if let Some(l) = new_data.get_mut(self.length / BVD::BIT_UNIT) {
            *l &= BVD::mask(self.length % BVD::BIT_UNIT);
        }
        BVD {
            data: new_data.into_boxed_slice(),
            length: self.length,
        }
    }
}

macro_rules! impl_shifts {({$($rhs:ty),+}) => {
    $(
        impl ShlAssign<$rhs> for BVD {
            fn shl_assign(&mut self, rhs: $rhs) {
                let shift = usize::try_from(rhs).map_or(0, |s| s);
                if shift == 0 {
                    return;
                }
                let mut new_idx = self.length;
                while new_idx > shift {
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

        impl ShlAssign<&$rhs> for BVD {
            fn shl_assign(&mut self, rhs: &$rhs) {
                self.shl_assign(*rhs);
            }
        }

        impl Shl<$rhs> for BVD {
            type Output = BVD;
            fn shl(mut self, rhs: $rhs) -> BVD {
                self.shl_assign(rhs);
                return self;
            }
        }

        impl Shl<&$rhs> for BVD {
            type Output = BVD;
            fn shl(mut self, rhs: &$rhs) -> BVD {
                self.shl_assign(rhs);
                return self;
            }
        }

        impl Shl<$rhs> for &BVD {
            type Output = BVD;
            fn shl(self, rhs: $rhs) -> BVD {
                let shift = usize::try_from(rhs).map_or(0, |s| s);
                let mut new_data: Vec<u64> = repeat(0).take(BVD::capacity_from_bit_len(self.length)).collect();
                let mut new_idx = self.length;
                while new_idx > shift {
                    let l = (new_idx.wrapping_sub(1) % BVD::BIT_UNIT + 1)
                            .min((new_idx - shift).wrapping_sub(1) % BVD::BIT_UNIT + 1);
                    new_idx -= l;
                    let old_idx = new_idx - shift;
                    new_data[new_idx / BVD::BIT_UNIT] |= ((self.data[old_idx / BVD::BIT_UNIT] >> (old_idx % BVD::BIT_UNIT)) & BVD::mask(l)) << (new_idx % BVD::BIT_UNIT);
                }
                BVD {
                    data: new_data.into_boxed_slice(),
                    length: self.length
                }
            }
        }

        impl Shl<&$rhs> for &BVD {
            type Output = BVD;
            fn shl(self, rhs: &$rhs) -> BVD {
                self.shl(*rhs)
            }
        }

        impl ShrAssign<$rhs> for BVD {
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

        impl ShrAssign<&$rhs> for BVD {
            fn shr_assign(&mut self, rhs: &$rhs) {
                self.shr_assign(*rhs);
            }
        }

        impl Shr<$rhs> for BVD {
            type Output = BVD;
            fn shr(mut self, rhs: $rhs) -> BVD {
                self.shr_assign(rhs);
                return self;
            }
        }

        impl Shr<&$rhs> for BVD {
            type Output = BVD;
            fn shr(mut self, rhs: &$rhs) -> BVD {
                self.shr_assign(rhs);
                return self;
            }
        }

        impl Shr<$rhs> for &BVD {
            type Output = BVD;
            fn shr(self, rhs: $rhs) -> BVD {
                let shift = usize::try_from(rhs).map_or(0, |s| s);
                let mut new_data: Vec<u64> = repeat(0).take(BVD::capacity_from_bit_len(self.length)).collect();
                let mut new_idx = 0;
                while new_idx + shift < self.length {
                    let old_idx = new_idx + shift;
                    let l = (BVD::BIT_UNIT - new_idx % BVD::BIT_UNIT)
                            .min(BVD::BIT_UNIT - old_idx % BVD::BIT_UNIT);
                    new_data[new_idx / BVD::BIT_UNIT] |= ((self.data[old_idx / BVD::BIT_UNIT] >> (old_idx % BVD::BIT_UNIT)) & BVD::mask(l)) << (new_idx % BVD::BIT_UNIT);
                    new_idx += l;
                }
                BVD {
                    data: new_data.into_boxed_slice(),
                    length: self.length
                }
            }
        }

        impl Shr<&$rhs> for &BVD {
            type Output = BVD;
            fn shr(self, rhs: &$rhs) -> BVD {
                self.shr(*rhs)
            }
        }
    )+
}}

impl_shifts!({u8, u16, u32, u64, u128, usize});

// ------------------------------------------------------------------------------------------------
// BVD - Arithmetic operators (assignment kind)
// ------------------------------------------------------------------------------------------------

macro_rules! impl_binop_assign {
    ($trait:ident, $method:ident) => {
        impl $trait<&BVD> for BVD {
            fn $method(&mut self, rhs: &BVD) {
                for i in 0..Self::capacity_from_bit_len(rhs.length) {
                    self.data[i].$method(rhs.data[i]);
                }
                for i in Self::capacity_from_bit_len(rhs.length)
                    ..Self::capacity_from_bit_len(self.length)
                {
                    self.data[i].$method(0);
                }
            }
        }

        impl $trait<BVD> for BVD {
            fn $method(&mut self, rhs: BVD) {
                self.$method(&rhs);
            }
        }

        impl<I: Integer, const N: usize> $trait<&BVF<I, N>> for BVD {
            fn $method(&mut self, rhs: &BVF<I, N>) {
                for i in 0..usize::min(IArray::int_len::<u64>(rhs), self.data.len()) {
                    self.data[i].$method(IArray::get_int::<u64>(rhs, i).unwrap());
                }
                for i in usize::min(IArray::int_len::<u64>(rhs), self.data.len())..self.data.len() {
                    self.data[i].$method(0);
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<BVF<I, N>> for BVD {
            fn $method(&mut self, rhs: BVF<I, N>) {
                self.$method(&rhs);
            }
        }

        impl $trait<&BV> for BVD {
            fn $method(&mut self, rhs: &BV) {
                match rhs {
                    BV::Fixed(bvf) => self.$method(bvf),
                    BV::Dynamic(bvd) => self.$method(bvd),
                }
            }
        }

        impl $trait<BV> for BVD {
            fn $method(&mut self, rhs: BV) {
                self.$method(&rhs);
            }
        }
    };
}

impl_binop_assign!(BitAndAssign, bitand_assign);
impl_binop_assign!(BitOrAssign, bitor_assign);
impl_binop_assign!(BitXorAssign, bitxor_assign);

macro_rules! impl_addsub_assign {
    ($trait:ident, $method:ident, $overflowing_method:ident) => {
        impl $trait<&BVD> for BVD {
            fn $method(&mut self, rhs: &BVD) {
                let mut carry = 0;
                for i in 0..Self::capacity_from_bit_len(rhs.length) {
                    let (d1, c1) = self.data[i].$overflowing_method(carry);
                    let (d2, c2) = d1.$overflowing_method(rhs.data[i]);
                    self.data[i] = d2;
                    carry = (c1 | c2) as u64;
                }
                for i in Self::capacity_from_bit_len(rhs.length)
                    ..Self::capacity_from_bit_len(self.length)
                {
                    let (d, c) = self.data[i].$overflowing_method(carry);
                    self.data[i] = d;
                    carry = c as u64;
                }
                if let Some(l) = self.data.get_mut(self.length / BVD::BIT_UNIT) {
                    *l &= Self::mask(self.length % BVD::BIT_UNIT);
                }
            }
        }

        impl $trait<BVD> for BVD {
            fn $method(&mut self, rhs: BVD) {
                self.$method(&rhs);
            }
        }

        impl<I: Integer, const N: usize> $trait<&BVF<I, N>> for BVD {
            fn $method(&mut self, rhs: &BVF<I, N>) {
                let mut carry = 0;
                for i in 0..IArray::int_len::<u64>(rhs) {
                    let (d1, c1) = self.data[i].$overflowing_method(carry);
                    let (d2, c2) = d1.$overflowing_method(IArray::get_int(rhs, i).unwrap());
                    self.data[i] = d2;
                    carry = (c1 | c2) as u64;
                }
                for i in IArray::int_len::<u64>(rhs)..Self::capacity_from_bit_len(self.length) {
                    let (d, c) = self.data[i].$overflowing_method(carry);
                    self.data[i] = d;
                    carry = c as u64;
                }
                if let Some(l) = self.data.get_mut(self.length / BVD::BIT_UNIT) {
                    *l &= Self::mask(self.length % BVD::BIT_UNIT);
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<BVF<I, N>> for BVD {
            fn $method(&mut self, rhs: BVF<I, N>) {
                self.$method(&rhs);
            }
        }

        impl $trait<&BV> for BVD {
            fn $method(&mut self, rhs: &BV) {
                match rhs {
                    BV::Fixed(bvf) => self.$method(bvf),
                    BV::Dynamic(bvd) => self.$method(bvd),
                }
            }
        }

        impl $trait<BV> for BVD {
            fn $method(&mut self, rhs: BV) {
                self.$method(&rhs);
            }
        }
    };
}

impl_addsub_assign!(AddAssign, add_assign, overflowing_add);
impl_addsub_assign!(SubAssign, sub_assign, overflowing_sub);

// ------------------------------------------------------------------------------------------------
// BVD - Arithmetic operators (general kind)
// ------------------------------------------------------------------------------------------------

macro_rules! impl_op {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl<T> $trait<T> for BVD
        where
            BVD: $assign_trait<T>,
        {
            type Output = BVD;
            fn $method(mut self, rhs: T) -> BVD {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl<T> $trait<T> for &BVD
        where
            BVD: $assign_trait<T>,
        {
            type Output = BVD;
            fn $method(self, rhs: T) -> BVD {
                let mut result = self.clone();
                result.$assign_method(rhs);
                return result;
            }
        }
    };
}

impl_op!(BitAnd, bitand, BitAndAssign, bitand_assign);
impl_op!(BitOr, bitor, BitOrAssign, bitor_assign);
impl_op!(BitXor, bitxor, BitXorAssign, bitxor_assign);
impl_op!(Add, add, AddAssign, add_assign);
impl_op!(Sub, sub, SubAssign, sub_assign);

// ------------------------------------------------------------------------------------------------
// BVD - Multiplication
// ------------------------------------------------------------------------------------------------

impl Mul<&BVD> for &BVD {
    type Output = BVD;
    fn mul(self, rhs: &BVD) -> BVD {
        let mut res = BVD::zeros(self.length);
        let len = BVD::capacity_from_bit_len(res.length);

        for i in 0..len {
            let mut carry = 0;
            for j in 0..(len - i) {
                let product = self.data[i].wmul(*rhs.data.get(j).unwrap_or(&0));
                carry = res.data[i + j].cadd(product.0, carry) + product.1;
            }
        }

        if let Some(l) = res.data.get_mut(res.length / BVD::BIT_UNIT) {
            *l &= BVD::mask(res.length % BVD::BIT_UNIT);
        }

        res
    }
}

impl Mul<BVD> for &BVD {
    type Output = BVD;
    fn mul(self, rhs: BVD) -> BVD {
        self.mul(&rhs)
    }
}

impl Mul<&BVD> for BVD {
    type Output = BVD;
    fn mul(self, rhs: &BVD) -> BVD {
        (&self).mul(rhs)
    }
}

impl Mul<BVD> for BVD {
    type Output = BVD;
    fn mul(self, rhs: BVD) -> BVD {
        (&self).mul(&rhs)
    }
}

impl<I: Integer, const N: usize> Mul<&BVF<I, N>> for &BVD {
    type Output = BVD;
    fn mul(self, rhs: &BVF<I, N>) -> BVD {
        let mut res = BVD::zeros(self.length);
        let len = IArray::int_len::<u64>(&res);

        for i in 0..len {
            let mut carry = 0;
            for j in 0..(len - i) {
                let product = self.data[i].wmul(IArray::get_int(rhs, j).unwrap_or(0));
                carry = res.data[i + j].cadd(product.0, carry) + product.1;
            }
        }

        if let Some(l) = res.data.get_mut(res.length / BVD::BIT_UNIT) {
            *l &= BVD::mask(res.length % BVD::BIT_UNIT);
        }

        res
    }
}

impl<I: Integer, const N: usize> Mul<BVF<I, N>> for &BVD {
    type Output = BVD;
    fn mul(self, rhs: BVF<I, N>) -> BVD {
        self.mul(&rhs)
    }
}

impl<I: Integer, const N: usize> Mul<&BVF<I, N>> for BVD {
    type Output = BVD;
    fn mul(self, rhs: &BVF<I, N>) -> BVD {
        (&self).mul(rhs)
    }
}

impl<I: Integer, const N: usize> Mul<BVF<I, N>> for BVD {
    type Output = BVD;
    fn mul(self, rhs: BVF<I, N>) -> BVD {
        (&self).mul(&rhs)
    }
}

impl Mul<&BV> for &BVD {
    type Output = BVD;
    fn mul(self, rhs: &BV) -> BVD {
        match rhs {
            BV::Fixed(bvf) => self.mul(bvf),
            BV::Dynamic(bvd) => self.mul(bvd),
        }
    }
}

impl Mul<BV> for &BVD {
    type Output = BVD;
    fn mul(self, rhs: BV) -> BVD {
        self.mul(&rhs)
    }
}

impl Mul<&BV> for BVD {
    type Output = BVD;
    fn mul(self, rhs: &BV) -> BVD {
        (&self).mul(rhs)
    }
}

impl Mul<BV> for BVD {
    type Output = BVD;
    fn mul(self, rhs: BV) -> BVD {
        (&self).mul(&rhs)
    }
}

impl MulAssign<&BVD> for BVD {
    fn mul_assign(&mut self, rhs: &BVD) {
        *self = Mul::mul(&*self, rhs);
    }
}

impl MulAssign<BVD> for BVD {
    fn mul_assign(&mut self, rhs: BVD) {
        *self = Mul::mul(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> MulAssign<&BVF<I, N>> for BVD {
    fn mul_assign(&mut self, rhs: &BVF<I, N>) {
        *self = Mul::mul(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> MulAssign<BVF<I, N>> for BVD {
    fn mul_assign(&mut self, rhs: BVF<I, N>) {
        *self = Mul::mul(&*self, &rhs);
    }
}

impl MulAssign<&BV> for BVD {
    fn mul_assign(&mut self, rhs: &BV) {
        *self = Mul::mul(&*self, rhs);
    }
}

impl MulAssign<BV> for BVD {
    fn mul_assign(&mut self, rhs: BV) {
        *self = Mul::mul(&*self, &rhs);
    }
}

// ------------------------------------------------------------------------------------------------
// BVF - Division
// ------------------------------------------------------------------------------------------------

impl Div<&BVD> for &BVD {
    type Output = BVD;

    fn div(self, rhs: &BVD) -> Self::Output {
        self.div_rem(rhs).0
    }
}

impl Div<BVD> for &BVD {
    type Output = BVD;
    fn div(self, rhs: BVD) -> BVD {
        self.div_rem(&rhs).0
    }
}

impl Div<&BVD> for BVD {
    type Output = BVD;
    fn div(self, rhs: &BVD) -> BVD {
        self.div_rem(rhs).0
    }
}

impl Div<BVD> for BVD {
    type Output = BVD;
    fn div(self, rhs: BVD) -> BVD {
        self.div_rem(&rhs).0
    }
}

impl<I: Integer, const N: usize> Div<&BVF<I, N>> for &BVD {
    type Output = BVD;

    fn div(self, rhs: &BVF<I, N>) -> BVD {
        self.div_rem(rhs).0
    }
}

impl<I: Integer, const N: usize> Div<BVF<I, N>> for &BVD {
    type Output = BVD;
    fn div(self, rhs: BVF<I, N>) -> BVD {
        self.div_rem(&rhs).0
    }
}

impl<I: Integer, const N: usize> Div<&BVF<I, N>> for BVD {
    type Output = BVD;
    fn div(self, rhs: &BVF<I, N>) -> BVD {
        self.div_rem(rhs).0
    }
}

impl<I: Integer, const N: usize> Div<BVF<I, N>> for BVD {
    type Output = BVD;
    fn div(self, rhs: BVF<I, N>) -> BVD {
        self.div_rem(&rhs).0
    }
}

impl Div<&BV> for &BVD {
    type Output = BVD;
    fn div(self, rhs: &BV) -> BVD {
        match rhs {
            BV::Fixed(bvf) => self.div_rem(bvf).0,
            BV::Dynamic(bvd) => self.div_rem(bvd).0,
        }
    }
}

impl Div<BV> for &BVD {
    type Output = BVD;
    fn div(self, rhs: BV) -> BVD {
        self.div(&rhs)
    }
}

impl Div<&BV> for BVD {
    type Output = BVD;
    fn div(self, rhs: &BV) -> BVD {
        (&self).div(rhs)
    }
}

impl Div<BV> for BVD {
    type Output = BVD;
    fn div(self, rhs: BV) -> BVD {
        (&self).div(&rhs)
    }
}

impl DivAssign<&BVD> for BVD {
    fn div_assign(&mut self, rhs: &BVD) {
        *self = Div::div(&*self, rhs);
    }
}

impl DivAssign<BVD> for BVD {
    fn div_assign(&mut self, rhs: BVD) {
        *self = Div::div(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> DivAssign<&BVF<I, N>> for BVD {
    fn div_assign(&mut self, rhs: &BVF<I, N>) {
        *self = Div::div(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> DivAssign<BVF<I, N>> for BVD {
    fn div_assign(&mut self, rhs: BVF<I, N>) {
        *self = Div::div(&*self, &rhs);
    }
}

impl DivAssign<&BV> for BVD {
    fn div_assign(&mut self, rhs: &BV) {
        *self = Div::div(&*self, rhs);
    }
}

impl DivAssign<BV> for BVD {
    fn div_assign(&mut self, rhs: BV) {
        *self = Div::div(&*self, &rhs);
    }
}

// ------------------------------------------------------------------------------------------------
// BVF - Division
// ------------------------------------------------------------------------------------------------

impl Rem<&BVD> for &BVD {
    type Output = BVD;
    fn rem(self, rhs: &BVD) -> Self::Output {
        self.div_rem(rhs).1
    }
}

impl Rem<BVD> for &BVD {
    type Output = BVD;
    fn rem(self, rhs: BVD) -> BVD {
        self.div_rem(&rhs).1
    }
}

impl Rem<&BVD> for BVD {
    type Output = BVD;
    fn rem(self, rhs: &BVD) -> BVD {
        self.div_rem(rhs).1
    }
}

impl Rem<BVD> for BVD {
    type Output = BVD;
    fn rem(self, rhs: BVD) -> BVD {
        self.div_rem(&rhs).1
    }
}

impl<I: Integer, const N: usize> Rem<&BVF<I, N>> for &BVD {
    type Output = BVD;
    fn rem(self, rhs: &BVF<I, N>) -> BVD {
        self.div_rem(rhs).1
    }
}

impl<I: Integer, const N: usize> Rem<BVF<I, N>> for &BVD {
    type Output = BVD;
    fn rem(self, rhs: BVF<I, N>) -> BVD {
        self.div_rem(&rhs).1
    }
}

impl<I: Integer, const N: usize> Rem<&BVF<I, N>> for BVD {
    type Output = BVD;
    fn rem(self, rhs: &BVF<I, N>) -> BVD {
        self.div_rem(rhs).1
    }
}

impl<I: Integer, const N: usize> Rem<BVF<I, N>> for BVD {
    type Output = BVD;
    fn rem(self, rhs: BVF<I, N>) -> BVD {
        self.div_rem(&rhs).1
    }
}

impl Rem<&BV> for &BVD {
    type Output = BVD;
    fn rem(self, rhs: &BV) -> BVD {
        match rhs {
            BV::Fixed(bvf) => self.div_rem(bvf).1,
            BV::Dynamic(bvd) => self.div_rem(bvd).1,
        }
    }
}

impl Rem<BV> for &BVD {
    type Output = BVD;
    fn rem(self, rhs: BV) -> BVD {
        self.rem(&rhs)
    }
}

impl Rem<&BV> for BVD {
    type Output = BVD;
    fn rem(self, rhs: &BV) -> BVD {
        (&self).rem(rhs)
    }
}

impl Rem<BV> for BVD {
    type Output = BVD;
    fn rem(self, rhs: BV) -> BVD {
        (&self).rem(&rhs)
    }
}

impl RemAssign<&BVD> for BVD {
    fn rem_assign(&mut self, rhs: &BVD) {
        *self = Rem::rem(&*self, rhs);
    }
}

impl RemAssign<BVD> for BVD {
    fn rem_assign(&mut self, rhs: BVD) {
        *self = Rem::rem(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> RemAssign<&BVF<I, N>> for BVD {
    fn rem_assign(&mut self, rhs: &BVF<I, N>) {
        *self = Rem::rem(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> RemAssign<BVF<I, N>> for BVD {
    fn rem_assign(&mut self, rhs: BVF<I, N>) {
        *self = Rem::rem(&*self, &rhs);
    }
}

impl RemAssign<&BV> for BVD {
    fn rem_assign(&mut self, rhs: &BV) {
        *self = Rem::rem(&*self, rhs);
    }
}

impl RemAssign<BV> for BVD {
    fn rem_assign(&mut self, rhs: BV) {
        *self = Rem::rem(&*self, &rhs);
    }
}
