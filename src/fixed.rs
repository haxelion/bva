use std::cmp::Ordering;
use std::fmt;
use std::iter::repeat;
use std::mem::size_of;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Range, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::auto::BV;
use crate::dynamic::BVD;
use crate::iter::BitIterator;
use crate::utils::{IArray, IArrayMut, Integer, StaticCast};
use crate::{Bit, BitVector, ConvertionError, Endianness};

pub type BV8 = BVF<u8, 1>;
pub type BV16 = BVF<u16, 1>;
pub type BV32 = BVF<u32, 1>;
pub type BV64 = BVF<u64, 1>;
pub type BV128 = BVF<u64, 2>;
pub type BV192 = BVF<u64, 3>;
pub type BV256 = BVF<u64, 4>;
pub type BV320 = BVF<u64, 5>;
pub type BV384 = BVF<u64, 6>;
pub type BV448 = BVF<u64, 7>;
pub type BV512 = BVF<u64, 8>;

// ------------------------------------------------------------------------------------------------
// Bit Vector Fixed allocation implementation
// ------------------------------------------------------------------------------------------------

/// A bit vector with fixed capacity.
#[derive(Copy, Clone, Debug)]
pub struct BVF<I: Integer, const N: usize> {
    data: [I; N],
    length: usize,
}

impl<I: Integer, const N: usize> BVF<I, N> {
    const BYTE_UNIT: usize = size_of::<I>();
    const NIBBLE_UNIT: usize = size_of::<I>() * 2;
    const BIT_UNIT: usize = size_of::<I>() * 8;

    pub const fn new(data: [I; N], length: usize) -> Self {
        Self { data, length }
    }

    pub const fn into_inner(self) -> ([I; N], usize) {
        (self.data, self.length)
    }

    pub const fn capacity() -> usize {
        size_of::<I>() * 8 * N
    }

    const fn capacity_from_bit_len(bit_length: usize) -> usize {
        (bit_length + Self::BIT_UNIT - 1) / Self::BIT_UNIT
    }

    fn mod2n(&mut self, n: usize) {
        for i in 0..N {
            self.data[i] &= I::mask(usize::min(
                n - usize::min(n, i * Self::BIT_UNIT),
                Self::BIT_UNIT,
            ));
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BVF - Integer Array traits
// ------------------------------------------------------------------------------------------------

impl<I: Integer, const N: usize> IArray for BVF<I, N> {
    type I = I;

    fn int_len<J: Integer>(&self) -> usize
    where
        I: StaticCast<J>,
    {
        (self.length + size_of::<J>() * 8 - 1) / (size_of::<J>() * 8)
    }

    fn get_int<J: Integer>(&self, idx: usize) -> Option<J>
    where
        I: StaticCast<J>,
    {
        if idx * J::BITS < self.length {
            IArray::get_int::<J>(self.data.as_ref(), idx)
                .map(|v| v & J::mask(self.length - idx * J::BITS))
        } else {
            None
        }
    }
}

impl<I: Integer, const N: usize> IArrayMut for BVF<I, N> {
    type I = I;

    fn set_int<J: Integer>(&mut self, idx: usize, v: J) -> Option<J>
    where
        I: StaticCast<J>,
    {
        if idx * J::BITS < self.length {
            IArrayMut::set_int::<J>(
                self.data.as_mut(),
                idx,
                v & J::mask(self.length - idx * J::BITS),
            )
        } else {
            None
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BVF - Bit Vector core trait
// ------------------------------------------------------------------------------------------------

impl<I: Integer, const N: usize> BitVector for BVF<I, N>
where
    I: StaticCast<I>,
{
    fn with_capacity(_length: usize) -> Self {
        Self::zeros(0)
    }
    fn zeros(length: usize) -> Self {
        assert!(length <= Self::capacity());
        Self {
            data: [I::ZERO; N],
            length,
        }
    }

    fn ones(length: usize) -> Self {
        assert!(length <= Self::capacity());
        let mut ones = Self {
            data: [I::MAX; N],
            length,
        };
        ones.mod2n(length);
        ones
    }

    fn capacity(&self) -> usize {
        BVF::<I, N>::capacity()
    }

    fn len(&self) -> usize {
        self.length
    }

    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError> {
        let length = string.as_ref().chars().count();
        if length > Self::capacity() {
            return Err(ConvertionError::NotEnoughCapacity);
        }
        let mut data = [I::ZERO; N];

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = (length - 1 - i) / Self::BIT_UNIT;
            data[j] = (data[j] << 1)
                | match c {
                    '0' => I::ZERO,
                    '1' => I::ONE,
                    _ => return Err(ConvertionError::InvalidFormat(i)),
                };
        }
        Ok(Self { data, length })
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError> {
        let length = string.as_ref().chars().count();
        if length * 4 > Self::capacity() {
            return Err(ConvertionError::NotEnoughCapacity);
        }
        let mut data = [I::ZERO; N];

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = (length - 1 - i) / Self::NIBBLE_UNIT;
            data[j] = (data[j] << 4)
                | match c.to_digit(16) {
                    Some(d) => I::cast_from(d as u8),
                    None => return Err(ConvertionError::InvalidFormat(i)),
                };
        }
        Ok(Self {
            data,
            length: length * 4,
        })
    }

    fn from_bytes<B: AsRef<[u8]>>(
        bytes: B,
        endianness: Endianness,
    ) -> Result<Self, ConvertionError> {
        let byte_length = bytes.as_ref().len();
        if byte_length * 8 > Self::capacity() {
            return Err(ConvertionError::NotEnoughCapacity);
        }
        let mut data = [I::ZERO; N];

        match endianness {
            Endianness::LE => {
                if size_of::<I>() == 1 {
                    for (i, b) in bytes.as_ref().iter().enumerate().rev() {
                        data[i] = I::cast_from(*b);
                    }
                } else {
                    for (i, b) in bytes.as_ref().iter().enumerate().rev() {
                        let j = i / Self::BYTE_UNIT;
                        data[j] = (data[j] << 8) | I::cast_from(*b);
                    }
                }
            }
            Endianness::BE => {
                if size_of::<I>() == 1 {
                    for (i, b) in bytes.as_ref().iter().enumerate() {
                        data[byte_length - 1 - i] = I::cast_from(*b);
                    }
                } else {
                    for (i, b) in bytes.as_ref().iter().enumerate() {
                        let j = (byte_length - 1 - i) / Self::BYTE_UNIT;
                        data[j] = (data[j] << 8) | I::cast_from(*b);
                    }
                }
            }
        }
        Ok(Self {
            data,
            length: byte_length * 8,
        })
    }

    fn to_vec(&self, endianness: Endianness) -> Vec<u8> {
        let num_bytes = (self.length + 7) / 8;
        let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
        match endianness {
            Endianness::LE => {
                for i in 0..num_bytes {
                    buf[i] =
                        (self.data[i / Self::BYTE_UNIT] >> ((i % Self::BYTE_UNIT) * 8)).cast_to();
                }
            }
            Endianness::BE => {
                for i in 0..num_bytes {
                    buf[num_bytes - i - 1] =
                        (self.data[i / Self::BYTE_UNIT] >> ((i % Self::BYTE_UNIT) * 8)).cast_to();
                }
            }
        }
        buf
    }

    fn read<R: std::io::Read>(
        reader: &mut R,
        length: usize,
        endianness: Endianness,
    ) -> std::io::Result<Self> {
        if length > Self::capacity() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                ConvertionError::NotEnoughCapacity,
            ));
        }
        let num_bytes = (length + 7) / 8;
        let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
        reader.read_exact(&mut buf[..])?;
        let mut bv = Self::from_bytes(&buf[..], endianness)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        if let Some(l) = bv.data.last_mut() {
            *l &= I::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }
        bv.length = length;
        Ok(bv)
    }

    fn write<W: std::io::Write>(
        &self,
        writer: &mut W,
        endianness: Endianness,
    ) -> std::io::Result<()> {
        return writer.write_all(self.to_vec(endianness).as_slice());
    }

    fn get(&self, index: usize) -> Bit {
        debug_assert!(index < self.length);
        (self.data[index / Self::BIT_UNIT] >> (index % Self::BIT_UNIT) & I::ONE).into()
    }

    fn set(&mut self, index: usize, bit: Bit) {
        debug_assert!(index < self.length);
        let b: I = (I::from(bit)) << (index % Self::BIT_UNIT);
        let mask: I = !(I::ONE << (index % Self::BIT_UNIT));
        self.data[index / Self::BIT_UNIT] = (self.data[index / Self::BIT_UNIT] & mask) | b;
    }

    fn copy_range(&self, range: Range<usize>) -> Self {
        debug_assert!(range.start <= self.len() && range.end <= self.len());
        let length = range.end - usize::min(range.start, range.end);
        let mut data = [I::ZERO; N];
        let offset = range.start / Self::BIT_UNIT;
        let slide = range.start % Self::BIT_UNIT;

        // If slide is 0 the left shift offset will be zero which is UB. Since we don't have a
        // checked variant, we have to duplicate the implementation
        if slide > 0 {
            for i in 0..Self::capacity_from_bit_len(length) {
                data[i] = (self.data[i + offset] >> slide)
                    | (*self.data.get(i + offset + 1).unwrap_or(&I::ZERO)
                        << (Self::BIT_UNIT - slide));
            }
        } else {
            data[..Self::capacity_from_bit_len(length)].copy_from_slice(
                &self.data[offset..(Self::capacity_from_bit_len(length) + offset)],
            );
        }

        if let Some(last) = data.get_mut(length / Self::BIT_UNIT) {
            *last &= I::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }

        BVF::<I, N> { data, length }
    }

    fn push(&mut self, bit: Bit) {
        debug_assert!(self.length < Self::capacity());
        self.length += 1;
        self.set(self.length - 1, bit);
    }

    fn pop(&mut self) -> Option<Bit> {
        let mut b = None;
        if self.length > 0 {
            b = Some(self.get(self.length - 1));
            self.set(self.length - 1, Bit::Zero);
            self.length -= 1;
        }
        b
    }

    fn resize(&mut self, new_length: usize, bit: Bit) {
        if new_length < self.length {
            for i in (new_length / Self::BIT_UNIT + 1)..Self::capacity_from_bit_len(self.length) {
                self.data[i] = I::ZERO;
            }
            if let Some(l) = self.data.get_mut(new_length / Self::BIT_UNIT) {
                *l &= I::mask(new_length % Self::BIT_UNIT);
            }
            self.length = new_length;
        } else if new_length > self.length {
            debug_assert!(new_length <= Self::capacity());
            let sign_pattern = match bit {
                Bit::Zero => I::MIN,
                Bit::One => I::MAX,
            };
            if let Some(l) = self.data.get_mut(self.length / Self::BIT_UNIT) {
                *l |= sign_pattern & !I::mask(self.length % Self::BIT_UNIT);
            }
            for i in (self.length / Self::BIT_UNIT + 1)..Self::capacity_from_bit_len(new_length) {
                self.data[i] = sign_pattern;
            }
            if let Some(l) = self.data.get_mut(new_length / Self::BIT_UNIT) {
                *l &= I::mask(new_length % Self::BIT_UNIT);
            }
            self.length = new_length;
        }
    }

    fn append<B: BitVector>(&mut self, suffix: &B) {
        let offset = self.length % u8::BITS as usize;
        let slide = self.length / u8::BITS as usize;
        self.resize(self.length + suffix.len(), Bit::Zero);
        if offset == 0 {
            let mut i = 0;
            while let Some(b) = suffix.get_int::<u8>(i) {
                self.set_int::<u8>(i + slide, b);
                i += 1;
            }
        } else if let Some(b) = suffix.get_int::<u8>(0) {
            self.set_int::<u8>(
                slide,
                self.get_int::<u8>(slide).unwrap_or(0) | (b << offset),
            );

            let rev_offset = u8::BITS as usize - offset;
            let mut i = 1;
            let mut prev = b;

            while let Some(b) = suffix.get_int::<u8>(i) {
                self.set_int::<u8>(i + slide, (prev >> rev_offset) | (b << offset));
                prev = b;
                i += 1;
            }

            self.set_int::<u8>(i + slide, prev >> rev_offset);
        }
    }

    fn prepend<B: BitVector>(&mut self, prefix: &B) {
        self.resize(self.length + prefix.len(), Bit::Zero);
        *self <<= prefix.len();
        let last = prefix.int_len::<u8>() - 1;

        for i in 0..last {
            self.set_int::<u8>(i, prefix.get_int::<u8>(i).unwrap());
        }

        self.set_int::<u8>(
            last,
            self.get_int::<u8>(last).unwrap() | prefix.get_int::<u8>(last).unwrap(),
        );
    }

    fn shl_in(&mut self, bit: Bit) -> Bit {
        let mut carry = bit;
        for i in 0..(self.length / Self::BIT_UNIT) {
            let b = self.data[i] >> (Self::BIT_UNIT - 1) & I::ONE;
            self.data[i] = self.data[i] << 1 | carry.into();
            carry = b.into();
        }
        if self.length % Self::BIT_UNIT != 0 {
            let i = self.length / Self::BIT_UNIT;
            let b = self.data[i] >> (self.length % Self::BIT_UNIT - 1) & I::ONE;
            self.data[i] =
                (self.data[i] << 1 | carry.into()) & I::mask(self.length % Self::BIT_UNIT);
            carry = b.into();
        }
        carry
    }

    fn shr_in(&mut self, bit: Bit) -> Bit {
        let mut carry = bit;
        if self.length % Self::BIT_UNIT != 0 {
            let i = self.length / Self::BIT_UNIT;
            let b = self.data[i] & I::ONE;
            self.data[i] = self.data[i] >> 1 | I::from(carry) << (self.length % Self::BIT_UNIT - 1);
            carry = b.into();
        }
        for i in (0..(self.length / Self::BIT_UNIT)).rev() {
            let b = self.data[i] & I::ONE;
            self.data[i] = self.data[i] >> 1 | I::from(carry) << (Self::BIT_UNIT - 1);
            carry = b.into();
        }
        carry
    }

    fn rotl(&mut self, rot: usize) {
        // TODO: optimize to do it in place
        let mut new_data = [I::ZERO; N];
        let mut old_idx = 0;
        while old_idx < self.length {
            let new_idx = (old_idx + rot) % self.length;
            let l = (Self::BIT_UNIT - new_idx % Self::BIT_UNIT)
                .min(Self::BIT_UNIT - old_idx % Self::BIT_UNIT)
                .min(self.length - new_idx)
                .min(self.length - old_idx);
            new_data[new_idx / Self::BIT_UNIT] |=
                ((self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & I::mask(l))
                    << (new_idx % Self::BIT_UNIT);
            old_idx += l;
        }
        self.data = new_data;
    }

    fn rotr(&mut self, rot: usize) {
        // TODO: optimize to do it in place
        let mut new_data = [I::ZERO; N];
        let mut new_idx = 0;
        while new_idx < self.length {
            let old_idx = (new_idx + rot) % self.length;
            let l = (Self::BIT_UNIT - new_idx % Self::BIT_UNIT)
                .min(Self::BIT_UNIT - old_idx % Self::BIT_UNIT)
                .min(self.length - new_idx)
                .min(self.length - old_idx);
            new_data[new_idx / Self::BIT_UNIT] |=
                ((self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & I::mask(l))
                    << (new_idx % Self::BIT_UNIT);
            new_idx += l;
        }
        self.data = new_data;
    }

    fn leading_zeros(&self) -> usize {
        let mut count = 0;
        let mut i = Self::capacity_from_bit_len(self.length);
        if i > 0 {
            let lastbit = (self.length - 1) % Self::BIT_UNIT + 1;
            let mut v = self.data[i - 1] & I::mask(lastbit);
            count = v.leading_zeros() - (Self::BIT_UNIT - lastbit);
            i -= 1;
            while v == I::ZERO && i > 0 {
                v = self.data[i - 1];
                count += v.leading_zeros();
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
            let mut v = self.data[i - 1] | !I::mask(lastbit);
            count = v.leading_ones() - (Self::BIT_UNIT - lastbit);
            i -= 1;
            while v == I::MAX && i > 0 {
                v = self.data[i - 1];
                count += v.leading_ones();
                i -= 1;
            }
        }
        count
    }

    fn trailing_zeros(&self) -> usize {
        let mut count = 0;
        let mut i = 0;
        if i < Self::capacity_from_bit_len(self.length) {
            let mut v = I::ZERO;
            while v == I::ZERO && i < Self::capacity_from_bit_len(self.length) - 1 {
                v = self.data[i];
                count += v.trailing_zeros();
                i += 1;
            }
            if v == I::ZERO {
                let lastbit = (self.length - 1) % Self::BIT_UNIT + 1;
                count += usize::min(self.data[i].trailing_zeros(), lastbit);
            }
        }
        count
    }

    fn trailing_ones(&self) -> usize {
        let mut count = 0;
        let mut i = 0;
        if i < Self::capacity_from_bit_len(self.length) {
            let mut v = I::MAX;
            while v == I::MAX && i < Self::capacity_from_bit_len(self.length) - 1 {
                v = self.data[i];
                count += v.trailing_ones();
                i += 1;
            }
            if v == I::MAX {
                let lastbit = (self.length - 1) % Self::BIT_UNIT + 1;
                count += usize::min(self.data[i].trailing_ones(), lastbit);
            }
        }
        count
    }

    fn is_zero(&self) -> bool {
        self.data.iter().all(|&v| v == I::ZERO)
    }

    fn div_rem<B: BitVector>(&self, divisor: &B) -> (Self, Self)
    where
        Self: for<'a> TryFrom<&'a B, Error: fmt::Debug>,
    {
        assert!(!divisor.is_zero(), "Division by zero");
        let mut rem = *self;
        let mut quotient = BVF::<I, N>::zeros(self.length);
        if divisor.significant_bits() > self.significant_bits() {
            return (quotient, rem);
        }

        let shift = self.significant_bits() - divisor.significant_bits();
        let mut divisor: BVF<I, N> = divisor.try_into().expect("divisor should fit in Self");
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
// BVF - Bit iterator trait
// ------------------------------------------------------------------------------------------------

impl<'a, I: Integer, const N: usize> IntoIterator for &'a BVF<I, N> {
    type Item = Bit;
    type IntoIter = BitIterator<'a, BVF<I, N>>;

    fn into_iter(self) -> Self::IntoIter {
        BitIterator::new(self)
    }
}

impl<I: Integer, const N: usize> FromIterator<Bit> for BVF<I, N>
where
    I: StaticCast<I>,
{
    fn from_iter<T: IntoIterator<Item = Bit>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut bv = Self::with_capacity(iter.size_hint().0);
        iter.for_each(|b| bv.push(b));
        bv
    }
}

impl<I: Integer, const N: usize> Extend<Bit> for BVF<I, N> {
    fn extend<T: IntoIterator<Item = Bit>>(&mut self, iter: T) {
        iter.into_iter().for_each(|b| self.push(b));
    }
}

// ------------------------------------------------------------------------------------------------
// BVF - Formatting traits
// ------------------------------------------------------------------------------------------------

impl<I: Integer, const N: usize> fmt::Binary for BVF<I, N>
where
    I: StaticCast<I>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut i = self.length;
        let mut s = String::with_capacity(self.length);

        while i > 0 && self.get(i - 1) == Bit::Zero {
            i -= 1;
        }
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

impl<I: Integer, const N: usize> fmt::Display for BVF<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let base = Self::try_from(10u8).expect("Should fit in any BVF type");
        let mut s = Vec::<char>::new();
        let mut quotient = *self;
        let mut remainder;

        while !quotient.is_zero() {
            (quotient, remainder) = quotient.div_rem::<BVF<I, N>>(&base);
            // Remainder of division by 10 will be a single digit
            s.push(char::from_digit(u32::try_from(&remainder).unwrap(), 10).unwrap());
        }
        if s.is_empty() {
            s.push('0');
        }

        f.pad_integral(true, "", s.iter().rev().collect::<String>().as_str())
    }
}

impl<I: Integer, const N: usize> fmt::Octal for BVF<I, N> {
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

impl<I: Integer, const N: usize> fmt::LowerHex for BVF<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const NIBBLE: [char; 16] = [
            '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
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

impl<I: Integer, const N: usize> fmt::UpperHex for BVF<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
// BVF - Comparison traits
// ------------------------------------------------------------------------------------------------

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> PartialEq<BVF<I1, N1>>
    for BVF<I2, N2>
where
    I1: StaticCast<I1>,
    I2: StaticCast<I1>,
{
    fn eq(&self, other: &BVF<I1, N1>) -> bool {
        for i in 0..usize::max(IArray::int_len::<I1>(self), IArray::int_len::<I1>(other)) {
            if IArray::get_int(self, i).unwrap_or(I1::ZERO)
                != IArray::get_int(other, i).unwrap_or(I1::ZERO)
            {
                return false;
            }
        }
        true
    }
}

impl<I: Integer, const N: usize> PartialEq<BVD> for BVF<I, N> {
    fn eq(&self, other: &BVD) -> bool {
        other.eq(self)
    }
}

impl<I: Integer, const N: usize> PartialEq<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn eq(&self, other: &BV) -> bool {
        other.eq(self)
    }
}

impl<I: Integer, const N: usize> Eq for BVF<I, N> where I: StaticCast<I> {}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> PartialOrd<BVF<I1, N1>>
    for BVF<I2, N2>
where
    I1: StaticCast<I1>,
    I2: StaticCast<I1>,
{
    fn partial_cmp(&self, other: &BVF<I1, N1>) -> Option<std::cmp::Ordering> {
        for i in (0..usize::max(IArray::int_len::<I1>(self), IArray::int_len::<I1>(other))).rev() {
            match IArray::get_int(self, i)
                .unwrap_or(I1::ZERO)
                .cmp(&IArray::get_int(other, i).unwrap_or(I1::ZERO))
            {
                Ordering::Equal => continue,
                ord => return Some(ord),
            }
        }
        Some(Ordering::Equal)
    }
}

impl<I: Integer, const N: usize> PartialOrd<BVD> for BVF<I, N> {
    fn partial_cmp(&self, other: &BVD) -> Option<Ordering> {
        other.partial_cmp(self).map(|o| o.reverse())
    }
}

impl<I: Integer, const N: usize> PartialOrd<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn partial_cmp(&self, other: &BV) -> Option<Ordering> {
        other.partial_cmp(self).map(|o| o.reverse())
    }
}

impl<I: Integer, const N: usize> Ord for BVF<I, N>
where
    I: StaticCast<I>,
{
    fn cmp(&self, other: &Self) -> Ordering {
        // Partial Cmp never returns None
        self.partial_cmp(other).unwrap()
    }
}

// ------------------------------------------------------------------------------------------------
// BVF - Conversion traits
// ------------------------------------------------------------------------------------------------

macro_rules! impl_tryfrom { ($($type:ty),+) => {
    $(
        impl<I: Integer, const N: usize> TryFrom<$type> for BVF<I, N>
            where I: StaticCast<$type>
        {
            type Error = ConvertionError;

            fn try_from(int: $type) -> Result<Self, Self::Error> {
                // Branch should be optimized at compile time
                if size_of::<I>() >= size_of::<$type>() {
                    let mut data = [I::ZERO; N];
                    data[0] = I::cast_from(int);
                    return Ok(BVF {
                        data,
                        length: <$type>::BITS as usize
                    });
                }
                else {
                    // Check if value overflow the bit vector
                    if (<$type>::BITS - int.leading_zeros()) as usize > Self::capacity() {
                        return Err(ConvertionError::NotEnoughCapacity);
                    }
                    let mut data = [I::ZERO; N];
                    for i in 0..N {
                        data[i] = I::cast_from(int.checked_shr((i * Self::BIT_UNIT) as u32).unwrap_or(0));
                    }
                    return Ok(BVF {
                        data,
                        length: usize::min(<$type>::BITS as usize, Self::capacity())
                    });
                }
            }
        }

        impl<I: Integer, const N: usize> TryFrom<&$type> for BVF<I, N>
            where I: StaticCast<$type>
        {
            type Error = ConvertionError;

            fn try_from(int: &$type) -> Result<Self, Self::Error> {
                Self::try_from(*int)
            }
        }

        impl<I: Integer, const N: usize> TryFrom<&BVF<I, N>> for $type
            where I: StaticCast<$type>
        {
            type Error = ConvertionError;
            fn try_from(bv: &BVF<I, N>) -> Result<Self, Self::Error> {
                // Check if the bit vector overflow I
                if bv.significant_bits() > <$type>::BITS as usize {
                    Err(ConvertionError::NotEnoughCapacity)
                }
                else {
                    Ok(IArray::get_int(bv, 0).unwrap())
                }
            }
        }

        impl<I: Integer, const N: usize> TryFrom<BVF<I, N>> for $type
            where I: StaticCast<$type>
        {
            type Error = ConvertionError;
            fn try_from(bv: BVF<I, N>) -> Result<Self, Self::Error> {
                Self::try_from(&bv)
            }
        }
    )+
}}

impl_tryfrom!(u8, u16, u32, u64, u128, usize);

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> TryFrom<&BVF<I1, N1>>
    for BVF<I2, N2>
where
    I1: StaticCast<I2>,
{
    type Error = ConvertionError;

    fn try_from(bvf: &BVF<I1, N1>) -> Result<Self, Self::Error> {
        if Self::capacity() < bvf.length {
            Err(ConvertionError::NotEnoughCapacity)
        } else {
            let mut data = [I2::ZERO; N2];
            for i in 0..usize::min(N2, IArray::int_len::<I2>(bvf)) {
                data[i] = IArray::get_int(bvf, i).unwrap();
            }
            Ok(BVF::<I2, N2> {
                data,
                length: bvf.length,
            })
        }
    }
}

impl<I: Integer, const N: usize> TryFrom<&BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Error = ConvertionError;
    fn try_from(bvd: &BVD) -> Result<Self, Self::Error> {
        if bvd.len() > BVF::<I, N>::capacity() {
            Err(ConvertionError::NotEnoughCapacity)
        } else {
            let mut data = [I::ZERO; N];
            for i in 0..N {
                data[i] = bvd.get_int(i).unwrap_or(I::ZERO);
            }
            Ok(BVF::<I, N> {
                data,
                length: bvd.len(),
            })
        }
    }
}

impl<I: Integer, const N: usize> TryFrom<BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Error = ConvertionError;
    fn try_from(bvd: BVD) -> Result<Self, Self::Error> {
        Self::try_from(&bvd)
    }
}

impl<I: Integer, const N: usize> TryFrom<&BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Error = ConvertionError;
    fn try_from(bv: &BV) -> Result<Self, Self::Error> {
        if bv.len() > BVF::<I, N>::capacity() {
            Err(ConvertionError::NotEnoughCapacity)
        } else {
            let mut data = [I::ZERO; N];
            for i in 0..IArray::int_len::<I>(bv) {
                data[i] = IArray::get_int(bv, i).unwrap();
            }
            Ok(BVF::<I, N> {
                data,
                length: bv.len(),
            })
        }
    }
}

impl<I: Integer, const N: usize> TryFrom<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Error = ConvertionError;
    fn try_from(bv: BV) -> Result<Self, Self::Error> {
        Self::try_from(&bv)
    }
}

// ------------------------------------------------------------------------------------------------
// BVF - Unary operator & shifts
// ------------------------------------------------------------------------------------------------

impl<I: Integer, const N: usize> Not for BVF<I, N> {
    type Output = BVF<I, N>;

    fn not(mut self) -> BVF<I, N> {
        for i in 0..N {
            self.data[i] = !self.data[i];
        }
        self.mod2n(self.length);
        self
    }
}

impl<I: Integer, const N: usize> Not for &BVF<I, N> {
    type Output = BVF<I, N>;

    fn not(self) -> BVF<I, N> {
        (*self).not()
    }
}

macro_rules! impl_shifts {({$($rhs:ty),+}) => {
    $(
        impl<I: Integer, const N: usize> ShlAssign<$rhs> for BVF<I, N> {
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
                    let d = (self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & I::mask(l);
                    self.data[new_idx / Self::BIT_UNIT] &= !(I::mask(l) << (new_idx % Self::BIT_UNIT));
                    self.data[new_idx / Self::BIT_UNIT] |=  d << (new_idx % Self::BIT_UNIT);
                }
                while new_idx > 0 {
                    let l = (new_idx.wrapping_sub(1) % Self::BIT_UNIT) + 1;
                    new_idx -= l;
                    self.data[new_idx / Self::BIT_UNIT] &= !(I::mask(l) << (new_idx % Self::BIT_UNIT));
                }
            }
        }


        impl<I: Integer, const N: usize> ShlAssign<&$rhs> for BVF<I, N> {
            fn shl_assign(&mut self, rhs: &$rhs) {
                self.shl_assign(*rhs);
            }
        }

        impl<I: Integer, const N: usize> Shl<$rhs> for BVF<I, N> {
            type Output = BVF<I, N>;
            fn shl(mut self, rhs: $rhs) -> Self {
                self.shl_assign(rhs);
                return self;
            }
        }

        impl<I: Integer, const N: usize> Shl<&$rhs> for BVF<I, N> {
            type Output = BVF<I, N>;
            fn shl(mut self, rhs: &$rhs) -> Self {
                self.shl_assign(rhs);
                return self;
            }
        }

        impl<I: Integer, const N: usize> Shl<$rhs> for &BVF<I, N> {
            type Output = BVF<I, N>;
            fn shl(self, rhs: $rhs) -> BVF<I, N> {
                return (*self).shl(rhs);
            }
        }

        impl<I: Integer, const N: usize> Shl<&$rhs> for &BVF<I, N> {
            type Output = BVF<I, N>;
            fn shl(self, rhs: &$rhs) -> BVF<I, N> {
                self.shl(*rhs)
            }
        }

        impl<I: Integer, const N: usize> ShrAssign<$rhs> for BVF<I, N> {
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
                    let d = (self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & I::mask(l);
                    self.data[new_idx / Self::BIT_UNIT] &= !(I::mask(l) << (new_idx % Self::BIT_UNIT));
                    self.data[new_idx / Self::BIT_UNIT] |= d << (new_idx % Self::BIT_UNIT);
                    new_idx += l;
                }
                while new_idx < self.length {
                    let l = Self::BIT_UNIT - new_idx % Self::BIT_UNIT;
                    self.data[new_idx / Self::BIT_UNIT] &= !(I::mask(l) << (new_idx % Self::BIT_UNIT));
                    new_idx += l;
                }
            }
        }

        impl<I: Integer, const N: usize> ShrAssign<&$rhs> for BVF<I, N> {
            fn shr_assign(&mut self, rhs: &$rhs) {
                self.shr_assign(*rhs);
            }
        }

        impl<I: Integer, const N: usize> Shr<$rhs> for BVF<I, N> {
            type Output = BVF<I, N>;
            fn shr(mut self, rhs: $rhs) -> Self {
                self.shr_assign(rhs);
                return self;
            }
        }

        impl<I: Integer, const N: usize> Shr<&$rhs> for BVF<I, N> {
            type Output = BVF<I, N>;
            fn shr(mut self, rhs: &$rhs) -> Self {
                self.shr_assign(rhs);
                return self;
            }
        }

        impl<I: Integer, const N: usize> Shr<$rhs> for &BVF<I, N> {
            type Output = BVF<I, N>;
            fn shr(self, rhs: $rhs) -> BVF<I, N> {
                return (*self).shr(rhs);
            }
        }

        impl<I: Integer, const N: usize> Shr<&$rhs> for &BVF<I, N> {
            type Output = BVF<I, N>;
            fn shr(self, rhs: &$rhs) -> BVF<I, N> {
                self.shr(*rhs)
            }
        }
    )+
}}

impl_shifts!({u8, u16, u32, u64, u128, usize});

// ------------------------------------------------------------------------------------------------
// Uint helper macro
// ------------------------------------------------------------------------------------------------

macro_rules! impl_op_uint {
    ($trait:ident, $method:ident, {$($uint:ty),+}) => {
        $(
            impl<I: Integer, const N: usize> $trait<&$uint> for &BVF<I, N>
            where
                u64: StaticCast<I>,
            {
                type Output = BVF<I, N>;
                fn $method(self, rhs: &$uint) -> Self::Output {
                    // All basic type should fit in 128 bits
                    let temp = BVF::<u64, 2>::try_from(*rhs).unwrap();
                    self.$method(temp)
                }
            }

            impl<I: Integer, const N: usize> $trait<$uint> for &BVF<I, N>
            where
                u64: StaticCast<I>,
            {
                type Output = BVF<I, N>;
                fn $method(self, rhs: $uint) -> Self::Output {
                    // All basic type should fit in 128 bits
                    let temp = BVF::<u64, 2>::try_from(rhs).unwrap();
                    self.$method(temp)
                }
            }

            impl<I: Integer, const N: usize> $trait<&$uint> for BVF<I, N>
            where
                u64: StaticCast<I>,
            {
                type Output = BVF<I, N>;
                fn $method(self, rhs: &$uint) -> Self::Output {
                    // All basic type should fit in 128 bits
                    let temp = BVF::<u64, 2>::try_from(*rhs).unwrap();
                    self.$method(temp)
                }
            }

            impl<I: Integer, const N: usize> $trait<$uint> for BVF<I, N>
            where
                u64: StaticCast<I>,
            {
                type Output = BVF<I, N>;
                fn $method(self, rhs: $uint) -> Self::Output {
                    // All basic type should fit in 128 bits
                    let temp = BVF::<u64, 2>::try_from(rhs).unwrap();
                    self.$method(temp)
                }
            }
        )+
    };
}

macro_rules! impl_op_assign_uint {
    ($trait:ident, $method:ident, {$($uint:ty),+}) => {
        $(
            impl<I: Integer, const N: usize> $trait<$uint> for BVF<I, N>
            where
                u64: StaticCast<I>
            {
                fn $method(&mut self, rhs: $uint) {
                    // All basic type should fit in 128 bits
                    let temp = BVF::<u64, 2>::try_from(rhs).unwrap();
                    self.$method(&temp);
                }
            }

            impl<I: Integer, const N: usize> $trait<&$uint> for BVF<I, N>
            where
                u64: StaticCast<I>
            {
                fn $method(&mut self, rhs: &$uint) {
                    // All basic type should fit in 128 bits
                    let temp = BVF::<u64, 2>::try_from(*rhs).unwrap();
                    self.$method(&temp);
                }
            }
        )+
    };
}

// ------------------------------------------------------------------------------------------------
// BVF - Arithmetic operators (assignment kind)
// ------------------------------------------------------------------------------------------------

macro_rules! impl_binop_assign {
    ($trait:ident, $method:ident, {$($uint:ty),+}) => {
        impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> $trait<&BVF<I2, N2>>
            for BVF<I1, N1>
        where
            I2: StaticCast<I1>,
        {
            fn $method(&mut self, rhs: &BVF<I2, N2>) {
                if size_of::<I1>() == size_of::<I2>() {
                    for i in 0..usize::min(N1, N2) {
                        self.data[i].$method(StaticCast::<I1>::cast_to(rhs.data[i]));
                    }
                    for i in N2..N1 {
                        self.data[i].$method(I1::ZERO);
                    }
                } else {
                    for i in 0..N1 {
                        self.data[i].$method(IArray::get_int(rhs, i).unwrap_or(I1::ZERO));
                    }
                }
            }
        }

        impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> $trait<BVF<I2, N2>>
            for BVF<I1, N1>
        where
            I2: StaticCast<I1>,
        {
            fn $method(&mut self, rhs: BVF<I2, N2>) {
                self.$method(&rhs);
            }
        }

        impl<I: Integer, const N: usize> $trait<&BVD> for BVF<I, N>
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, rhs: &BVD) {
                for i in 0..N {
                    self.data[i].$method(IArray::get_int(rhs, i).unwrap_or(I::ZERO));
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<BVD> for BVF<I, N>
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, rhs: BVD) {
                self.$method(&rhs);
            }
        }

        impl<I: Integer, const N: usize> $trait<&BV> for BVF<I, N>
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, rhs: &BV) {
                match rhs {
                    BV::Fixed(bvf) => self.$method(bvf),
                    BV::Dynamic(bvd) => self.$method(bvd),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<BV> for BVF<I, N>
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, rhs: BV) {
                self.$method(&rhs);
            }
        }

        impl_op_assign_uint!($trait, $method, {$($uint),+});
    };
}

impl_binop_assign!(BitAndAssign, bitand_assign, {u8, u16, u32, u64, usize, u128});
impl_binop_assign!(BitOrAssign, bitor_assign, {u8, u16, u32, u64, usize, u128});
impl_binop_assign!(BitXorAssign, bitxor_assign, {u8, u16, u32, u64, usize, u128});

macro_rules! impl_addsub_assign {
    ($trait:ident, $method:ident, $carry_method:ident, {$($uint:ty),+}) => {
        impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> $trait<&BVF<I2, N2>>
            for BVF<I1, N1>
        where
            I2: StaticCast<I1>,
        {
            fn $method(&mut self, rhs: &BVF<I2, N2>) {
                if size_of::<I1>() == size_of::<I2>() {
                    let mut carry = I1::ZERO;

                    for i in 0..usize::min(N1, N2) {
                        carry = self.data[i]
                            .$carry_method(StaticCast::<I1>::cast_to(rhs.data[i]), carry);
                    }
                    for i in N2..N1 {
                        carry = self.data[i].$carry_method(I1::ZERO, carry);
                    }
                    self.mod2n(self.length);
                } else {
                    let mut carry = I1::ZERO;
                    for i in 0..N1 {
                        carry = self.data[i]
                            .$carry_method(IArray::get_int(rhs, i).unwrap_or(I1::ZERO), carry);
                    }
                    self.mod2n(self.length);
                }
            }
        }

        impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> $trait<BVF<I2, N2>>
            for BVF<I1, N1>
        where
            I2: StaticCast<I1>,
        {
            fn $method(&mut self, rhs: BVF<I2, N2>) {
                self.$method(&rhs);
            }
        }

        impl<I: Integer, const N: usize> $trait<&BVD> for BVF<I, N>
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, rhs: &BVD) {
                let mut carry = I::ZERO;
                for i in 0..N {
                    carry = self.data[i]
                        .$carry_method(IArray::get_int(rhs, i).unwrap_or(I::ZERO), carry);
                }
                self.mod2n(self.length);
            }
        }

        impl<I: Integer, const N: usize> $trait<BVD> for BVF<I, N>
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, rhs: BVD) {
                self.$method(&rhs);
            }
        }

        impl<I: Integer, const N: usize> $trait<&BV> for BVF<I, N>
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, rhs: &BV) {
                match rhs {
                    BV::Fixed(bvf) => self.$method(bvf),
                    BV::Dynamic(bvd) => self.$method(bvd),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<BV> for BVF<I, N>
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, rhs: BV) {
                self.$method(&rhs);
            }
        }

        impl_op_assign_uint!($trait, $method, {$($uint),+});
    };
}

impl_addsub_assign!(AddAssign, add_assign, cadd, {u8, u16, u32, u64, usize, u128});
impl_addsub_assign!(SubAssign, sub_assign, csub, {u8, u16, u32, u64, usize, u128});

// ------------------------------------------------------------------------------------------------
// BVF - Arithmetic operators (general kind)
// ------------------------------------------------------------------------------------------------

macro_rules! impl_op {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl<T, I: Integer, const N: usize> $trait<T> for BVF<I, N>
        where
            BVF<I, N>: $assign_trait<T>,
        {
            type Output = BVF<I, N>;
            fn $method(mut self, rhs: T) -> BVF<I, N> {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl<T, I: Integer, const N: usize> $trait<T> for &BVF<I, N>
        where
            BVF<I, N>: $assign_trait<T>,
        {
            type Output = BVF<I, N>;
            fn $method(self, rhs: T) -> BVF<I, N> {
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
// BVF - Multiplication
// ------------------------------------------------------------------------------------------------

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Mul<&BVF<I2, N2>> for &BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn mul(self, rhs: &BVF<I2, N2>) -> BVF<I1, N1> {
        let mut res = BVF::<I1, N1>::zeros(self.length);
        let len = IArray::int_len::<I1>(&res);
        for i in 0..len {
            let mut carry = I1::ZERO;
            for j in 0..(len - i) {
                let product = self.data[i].wmul(IArray::get_int(rhs, j).unwrap_or(I1::ZERO));
                carry = res.data[i + j].cadd(product.0, carry) + product.1;
            }
        }

        res.mod2n(self.length);
        res
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Mul<BVF<I2, N2>> for &BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn mul(self, rhs: BVF<I2, N2>) -> BVF<I1, N1> {
        self.mul(&rhs)
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Mul<&BVF<I2, N2>> for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn mul(self, rhs: &BVF<I2, N2>) -> BVF<I1, N1> {
        (&self).mul(rhs)
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Mul<BVF<I2, N2>> for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn mul(self, rhs: BVF<I2, N2>) -> BVF<I1, N1> {
        (&self).mul(&rhs)
    }
}

impl<I: Integer, const N: usize> Mul<&BVD> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn mul(self, rhs: &BVD) -> BVF<I, N> {
        let mut res = BVF::<I, N>::zeros(self.length);
        let len = IArray::int_len::<I>(&res);
        for i in 0..len {
            let mut carry = I::ZERO;
            for j in 0..(len - i) {
                let product = self.data[i].wmul(IArray::get_int(rhs, j).unwrap_or(I::ZERO));
                carry = res.data[i + j].cadd(product.0, carry) + product.1;
            }
        }

        res.mod2n(self.length);
        res
    }
}

impl<I: Integer, const N: usize> Mul<BVD> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn mul(self, rhs: BVD) -> BVF<I, N> {
        self.mul(&rhs)
    }
}

impl<I: Integer, const N: usize> Mul<&BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn mul(self, rhs: &BVD) -> BVF<I, N> {
        (&self).mul(rhs)
    }
}

impl<I: Integer, const N: usize> Mul<BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn mul(self, rhs: BVD) -> BVF<I, N> {
        (&self).mul(&rhs)
    }
}

impl<I: Integer, const N: usize> Mul<&BV> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn mul(self, rhs: &BV) -> Self::Output {
        match rhs {
            BV::Fixed(bvf) => self.mul(bvf),
            BV::Dynamic(bvd) => self.mul(bvd),
        }
    }
}

impl<I: Integer, const N: usize> Mul<&BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn mul(self, rhs: &BV) -> Self::Output {
        (&self).mul(rhs)
    }
}

impl<I: Integer, const N: usize> Mul<BV> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn mul(self, rhs: BV) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<I: Integer, const N: usize> Mul<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn mul(self, rhs: BV) -> Self::Output {
        (&self).mul(&rhs)
    }
}

impl_op_uint!(Mul, mul, {u8, u16, u32, u64, usize, u128});

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> MulAssign<&BVF<I2, N2>>
    for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    fn mul_assign(&mut self, rhs: &BVF<I2, N2>) {
        *self = Mul::mul(&*self, rhs);
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> MulAssign<BVF<I2, N2>>
    for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    fn mul_assign(&mut self, rhs: BVF<I2, N2>) {
        *self = Mul::mul(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> MulAssign<&BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn mul_assign(&mut self, rhs: &BVD) {
        *self = Mul::mul(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> MulAssign<BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn mul_assign(&mut self, rhs: BVD) {
        *self = Mul::mul(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> MulAssign<&BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn mul_assign(&mut self, rhs: &BV) {
        *self = Mul::mul(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> MulAssign<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn mul_assign(&mut self, rhs: BV) {
        *self = Mul::mul(&*self, &rhs);
    }
}

impl_op_assign_uint!(MulAssign, mul_assign, {u8, u16, u32, u64, usize, u128});

// ------------------------------------------------------------------------------------------------
// BVF - Division
// ------------------------------------------------------------------------------------------------

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Div<&BVF<I2, N2>> for &BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn div(self, rhs: &BVF<I2, N2>) -> Self::Output {
        self.div_rem::<BVF<I2, N2>>(rhs).0
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Div<BVF<I2, N2>> for &BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn div(self, rhs: BVF<I2, N2>) -> Self::Output {
        self.div_rem::<BVF<I2, N2>>(&rhs).0
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Div<&BVF<I2, N2>> for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn div(self, rhs: &BVF<I2, N2>) -> Self::Output {
        self.div_rem::<BVF<I2, N2>>(rhs).0
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Div<BVF<I2, N2>> for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn div(self, rhs: BVF<I2, N2>) -> Self::Output {
        self.div_rem::<BVF<I2, N2>>(&rhs).0
    }
}

impl<I: Integer, const N: usize> Div<&BVD> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn div(self, rhs: &BVD) -> Self::Output {
        self.div_rem::<BVD>(rhs).0
    }
}

impl<I1: Integer, const N1: usize> Div<BVD> for &BVF<I1, N1>
where
    u64: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn div(self, rhs: BVD) -> Self::Output {
        self.div_rem::<BVD>(&rhs).0
    }
}

impl<I1: Integer, const N1: usize> Div<&BVD> for BVF<I1, N1>
where
    u64: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn div(self, rhs: &BVD) -> Self::Output {
        self.div_rem::<BVD>(rhs).0
    }
}

impl<I1: Integer, const N1: usize> Div<BVD> for BVF<I1, N1>
where
    u64: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn div(self, rhs: BVD) -> Self::Output {
        self.div_rem::<BVD>(&rhs).0
    }
}

impl<I: Integer, const N: usize> Div<&BV> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn div(self, rhs: &BV) -> Self::Output {
        match rhs {
            BV::Fixed(bvf) => self.div_rem::<crate::auto::BVP>(bvf).0,
            BV::Dynamic(bvd) => self.div_rem::<BVD>(bvd).0,
        }
    }
}

impl<I: Integer, const N: usize> Div<&BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn div(self, rhs: &BV) -> Self::Output {
        (&self).div(rhs)
    }
}

impl<I: Integer, const N: usize> Div<BV> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn div(self, rhs: BV) -> Self::Output {
        self.div(&rhs)
    }
}

impl<I: Integer, const N: usize> Div<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn div(self, rhs: BV) -> Self::Output {
        (&self).div(&rhs)
    }
}

impl_op_uint!(Div, div, {u8, u16, u32, u64, usize, u128});

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> DivAssign<&BVF<I2, N2>>
    for BVF<I1, N1>
where
    I1: StaticCast<I2>,
    I2: StaticCast<I1>,
{
    fn div_assign(&mut self, rhs: &BVF<I2, N2>) {
        *self = Div::div(&*self, rhs);
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> DivAssign<BVF<I2, N2>>
    for BVF<I1, N1>
where
    I1: StaticCast<I2>,
    I2: StaticCast<I1>,
{
    fn div_assign(&mut self, rhs: BVF<I2, N2>) {
        *self = Div::div(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> DivAssign<&BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn div_assign(&mut self, rhs: &BVD) {
        *self = Div::div(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> DivAssign<BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn div_assign(&mut self, rhs: BVD) {
        *self = Div::div(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> DivAssign<&BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn div_assign(&mut self, rhs: &BV) {
        *self = Div::div(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> DivAssign<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn div_assign(&mut self, rhs: BV) {
        *self = Div::div(&*self, &rhs);
    }
}

impl_op_assign_uint!(DivAssign, div_assign, {u8, u16, u32, u64, usize, u128});

// ------------------------------------------------------------------------------------------------
// BVF - Remainder
// ------------------------------------------------------------------------------------------------

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Rem<&BVF<I2, N2>> for &BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn rem(self, rhs: &BVF<I2, N2>) -> Self::Output {
        self.div_rem::<BVF<I2, N2>>(rhs).1
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Rem<BVF<I2, N2>> for &BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn rem(self, rhs: BVF<I2, N2>) -> Self::Output {
        self.div_rem::<BVF<I2, N2>>(&rhs).1
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Rem<&BVF<I2, N2>> for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn rem(self, rhs: &BVF<I2, N2>) -> Self::Output {
        self.div_rem::<BVF<I2, N2>>(rhs).1
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Rem<BVF<I2, N2>> for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn rem(self, rhs: BVF<I2, N2>) -> Self::Output {
        self.div_rem::<BVF<I2, N2>>(&rhs).1
    }
}

impl<I: Integer, const N: usize> Rem<&BVD> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn rem(self, rhs: &BVD) -> Self::Output {
        self.div_rem::<BVD>(rhs).1
    }
}

impl<I1: Integer, const N1: usize> Rem<BVD> for &BVF<I1, N1>
where
    u64: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn rem(self, rhs: BVD) -> Self::Output {
        self.div_rem::<BVD>(&rhs).1
    }
}

impl<I1: Integer, const N1: usize> Rem<&BVD> for BVF<I1, N1>
where
    u64: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn rem(self, rhs: &BVD) -> Self::Output {
        self.div_rem::<BVD>(rhs).1
    }
}

impl<I1: Integer, const N1: usize> Rem<BVD> for BVF<I1, N1>
where
    u64: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn rem(self, rhs: BVD) -> Self::Output {
        self.div_rem::<BVD>(&rhs).1
    }
}

impl<I: Integer, const N: usize> Rem<&BV> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn rem(self, rhs: &BV) -> Self::Output {
        match rhs {
            BV::Fixed(bvf) => self.div_rem::<crate::auto::BVP>(bvf).1,
            BV::Dynamic(bvd) => self.div_rem::<BVD>(bvd).1,
        }
    }
}

impl<I: Integer, const N: usize> Rem<&BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn rem(self, rhs: &BV) -> Self::Output {
        (&self).rem(rhs)
    }
}

impl<I: Integer, const N: usize> Rem<BV> for &BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn rem(self, rhs: BV) -> Self::Output {
        self.rem(&rhs)
    }
}

impl<I: Integer, const N: usize> Rem<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Output = BVF<I, N>;
    fn rem(self, rhs: BV) -> Self::Output {
        (&self).rem(&rhs)
    }
}

impl_op_uint!(Rem, rem, {u8, u16, u32, u64, usize, u128});

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> RemAssign<&BVF<I2, N2>>
    for BVF<I1, N1>
where
    I1: StaticCast<I2>,
    I2: StaticCast<I1>,
{
    fn rem_assign(&mut self, rhs: &BVF<I2, N2>) {
        *self = Rem::rem(&*self, rhs);
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> RemAssign<BVF<I2, N2>>
    for BVF<I1, N1>
where
    I1: StaticCast<I2>,
    I2: StaticCast<I1>,
{
    fn rem_assign(&mut self, rhs: BVF<I2, N2>) {
        *self = Rem::rem(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> RemAssign<&BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn rem_assign(&mut self, rhs: &BVD) {
        *self = Rem::rem(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> RemAssign<BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn rem_assign(&mut self, rhs: BVD) {
        *self = Rem::rem(&*self, &rhs);
    }
}

impl<I: Integer, const N: usize> RemAssign<&BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn rem_assign(&mut self, rhs: &BV) {
        *self = Rem::rem(&*self, rhs);
    }
}

impl<I: Integer, const N: usize> RemAssign<BV> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    fn rem_assign(&mut self, rhs: BV) {
        *self = Rem::rem(&*self, &rhs);
    }
}

impl_op_assign_uint!(RemAssign, rem_assign, {u8, u16, u32, u64, usize, u128});
