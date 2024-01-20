use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::iter::repeat;
use std::mem::size_of;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Mul, MulAssign,
    Not, Range, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::dynamic::BVD;
use crate::iter::BitIterator;
use crate::utils::{IArray, IArrayMut, Integer, StaticCast};
use crate::{Bit, BitVector, ConvertError, Endianness};

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

#[derive(Copy, Clone, Debug)]
pub struct BVF<I: Integer, const N: usize> {
    data: [I; N],
    length: usize,
}

impl<I: Integer, const N: usize> BVF<I, N> {
    const BYTE_UNIT: usize = size_of::<I>();
    const NIBBLE_UNIT: usize = size_of::<I>() * 2;
    const BIT_UNIT: usize = size_of::<I>() * 8;

    pub const fn capacity() -> usize {
        size_of::<I>() * 8 * N
    }

    const fn capacity_from_bit_len(bit_length: usize) -> usize {
        (bit_length + Self::BIT_UNIT - 1) / Self::BIT_UNIT
    }

    fn mask(length: usize) -> I {
        // Re-implementation of checked_shr since we don't have a generic trait for it.
        if length == 0 {
            I::ZERO
        } else {
            I::MAX.shr(Self::BIT_UNIT - length)
        }
    }

    fn mod2n(&mut self, n: usize) {
        for i in 0..N {
            self.data[i] &= Self::mask(usize::min(
                n - usize::min(n, i * Self::BIT_UNIT),
                Self::BIT_UNIT,
            ));
        }
    }
}

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

    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertError> {
        let length = string.as_ref().chars().count();
        if length > Self::capacity() {
            return Err(ConvertError::NotEnoughCapacity);
        }
        let mut data = [I::ZERO; N];

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = (length - 1 - i) / Self::BIT_UNIT;
            data[j] = (data[j] << 1)
                | match c {
                    '0' => I::ZERO,
                    '1' => I::ONE,
                    _ => return Err(ConvertError::InvalidFormat(i)),
                };
        }
        Ok(Self { data, length })
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertError> {
        let length = string.as_ref().chars().count();
        if length * 4 > Self::capacity() {
            return Err(ConvertError::NotEnoughCapacity);
        }
        let mut data = [I::ZERO; N];

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = (length - 1 - i) / Self::NIBBLE_UNIT;
            data[j] = (data[j] << 4)
                | match c.to_digit(16) {
                    Some(d) => I::cast_from(d as u8),
                    None => return Err(ConvertError::InvalidFormat(i)),
                };
        }
        Ok(Self {
            data,
            length: length * 4,
        })
    }

    fn from_bytes<B: AsRef<[u8]>>(bytes: B, endianness: Endianness) -> Result<Self, ConvertError> {
        let byte_length = bytes.as_ref().len();
        if byte_length * 8 > Self::capacity() {
            return Err(ConvertError::NotEnoughCapacity);
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
                ConvertError::NotEnoughCapacity,
            ));
        }
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

    fn copy_slice(&self, range: Range<usize>) -> Self {
        debug_assert!(range.start < self.len() && range.end <= self.len());
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

        if let Some(last) = data.get_mut(Self::capacity_from_bit_len(length)) {
            *last &= Self::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
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
                *l &= Self::mask(new_length % Self::BIT_UNIT);
            }
            self.length = new_length;
        } else if new_length > self.length {
            debug_assert!(new_length <= Self::capacity());
            let sign_pattern = match bit {
                Bit::Zero => I::MIN,
                Bit::One => I::MAX,
            };
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
            let b = self.data[i] >> (Self::BIT_UNIT - 1) & I::ONE;
            self.data[i] = self.data[i] << 1 | carry.into();
            carry = b.into();
        }
        if self.length % Self::BIT_UNIT != 0 {
            let i = self.length / Self::BIT_UNIT;
            let b = self.data[i] >> (self.length % Self::BIT_UNIT - 1) & I::ONE;
            self.data[i] =
                (self.data[i] << 1 | carry.into()) & Self::mask(self.length % Self::BIT_UNIT);
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
            new_data[new_idx / Self::BIT_UNIT] |= ((self.data[old_idx / Self::BIT_UNIT]
                >> (old_idx % Self::BIT_UNIT))
                & Self::mask(l))
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
            new_data[new_idx / Self::BIT_UNIT] |= ((self.data[old_idx / Self::BIT_UNIT]
                >> (old_idx % Self::BIT_UNIT))
                & Self::mask(l))
                << (new_idx % Self::BIT_UNIT);
            new_idx += l;
        }
        self.data = new_data;
    }

    fn len(&self) -> usize {
        self.length
    }

    fn iter(&self) -> BitIterator<'_, Self> {
        self.into_iter()
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> PartialEq<BVF<I1, N1>>
    for BVF<I2, N2>
where
    I1: StaticCast<I1>,
    I2: StaticCast<I1>,
{
    fn eq(&self, other: &BVF<I1, N1>) -> bool {
        for i in 0..usize::max(IArray::<I1>::int_len(self), IArray::<I1>::int_len(self)) {
            if IArray::<I1>::get_int(self, i).unwrap_or(I1::ZERO)
                != IArray::<I1>::get_int(other, i).unwrap_or(I1::ZERO)
            {
                return false;
            }
        }
        true
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
        for i in (0..usize::max(IArray::<I1>::int_len(self), IArray::<I1>::int_len(other))).rev() {
            match IArray::<I1>::get_int(self, i)
                .unwrap_or(I1::ZERO)
                .cmp(&IArray::<I1>::get_int(other, i).unwrap_or(I1::ZERO))
            {
                Ordering::Equal => continue,
                ord => return Some(ord),
            }
        }
        Some(Ordering::Equal)
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

impl<I: Integer, const N: usize> fmt::Binary for BVF<I, N>
where
    I: StaticCast<I>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::with_capacity(self.length);
        for i in (0..self.length).rev() {
            match self.get(i) {
                Bit::Zero => s.push('0'),
                Bit::One => s.push('1'),
            }
        }
        if f.alternate() {
            write!(f, "0b{}", s.as_str())
        } else {
            write!(f, "{}", s.as_str())
        }
    }
}

impl<I: Integer, const N: usize> fmt::Display for BVF<I, N> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: waiting for div and mod operations
        todo!()
    }
}

impl<I: Integer, const N: usize> fmt::Octal for BVF<I, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const SEMI_NIBBLE: [char; 8] = ['0', '1', '2', '3', '4', '5', '6', '7'];
        let length = (self.length + 2) / 3;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            let semi_nibble = StaticCast::<u8>::cast_to(
                self.data[i / Self::NIBBLE_UNIT] >> ((i % Self::NIBBLE_UNIT) * 4),
            ) & 0x7;
            s.push(SEMI_NIBBLE[semi_nibble as usize]);
        }
        if f.alternate() {
            write!(f, "0x{}", s.as_str())
        } else {
            write!(f, "{}", s.as_str())
        }
    }
}

impl<I: Integer, const N: usize> fmt::LowerHex for BVF<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const NIBBLE: [char; 16] = [
            '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
        ];
        let length = (self.length + 3) / 4;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            let nibble = StaticCast::<u8>::cast_to(
                self.data[i / Self::NIBBLE_UNIT] >> ((i % Self::NIBBLE_UNIT) * 4),
            ) & 0xf;
            s.push(NIBBLE[nibble as usize]);
        }
        if f.alternate() {
            write!(f, "0x{}", s.as_str())
        } else {
            write!(f, "{}", s.as_str())
        }
    }
}

impl<I: Integer, const N: usize> fmt::UpperHex for BVF<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const NIBBLE: [char; 16] = [
            '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F',
        ];
        let length = (self.length + 3) / 4;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            let nibble = StaticCast::<u8>::cast_to(
                self.data[i / Self::NIBBLE_UNIT] >> ((i % Self::NIBBLE_UNIT) * 4),
            ) & 0xf;
            s.push(NIBBLE[nibble as usize]);
        }
        if f.alternate() {
            write!(f, "0x{}", s.as_str())
        } else {
            write!(f, "{}", s.as_str())
        }
    }
}

macro_rules! impl_tryfrom { ($($type:ty),+) => {
    $(
        impl<I: Integer, const N: usize> TryFrom<$type> for BVF<I, N>
            where I: StaticCast<$type>
        {
            type Error = ConvertError;

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
                    if <$type>::BITS as usize > Self::capacity() && int.shr(Self::capacity()) != 0 {
                        return Err(ConvertError::NotEnoughCapacity);
                    }
                    let mut data = [I::ZERO; N];
                    for i in 0..N {
                        data[i] = I::cast_from(int.shr(i * Self::BIT_UNIT));
                    }
                    return Ok(BVF {
                        data,
                        length: Self::capacity()
                    });
                }
            }
        }

        impl<I: Integer, const N: usize> TryFrom<&'_ BVF<I, N>> for $type
            where I: StaticCast<$type>
        {
            type Error = ConvertError;
            fn try_from(bv: &'_ BVF<I, N>) -> Result<Self, Self::Error> {
                // Check if the bit vector overflow I
                if bv.length > <$type>::BITS as usize {
                    Err(ConvertError::NotEnoughCapacity)
                }
                else {
                    Ok(IArray::<$type>::get_int(bv, 0).unwrap())
                }
            }
        }

        impl<I: Integer, const N: usize> TryFrom<BVF<I, N>> for $type
            where I: StaticCast<$type>
        {
            type Error = ConvertError;
            fn try_from(bv: BVF<I, N>) -> Result<Self, Self::Error> {
                Self::try_from(&bv)
            }
        }
    )+
}}

impl_tryfrom!(u8, u16, u32, u64, u128, usize);

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> TryFrom<&'_ BVF<I1, N1>>
    for BVF<I2, N2>
where
    I1: StaticCast<I2>,
{
    type Error = ConvertError;

    fn try_from(bvd: &'_ BVF<I1, N1>) -> Result<Self, Self::Error> {
        if Self::capacity() < bvd.length {
            Err(ConvertError::NotEnoughCapacity)
        } else {
            let mut data = [I2::ZERO; N2];
            for i in 0..usize::min(N2, IArray::<I2>::int_len(bvd)) {
                data[i] = IArray::<I2>::get_int(bvd, i).unwrap();
            }
            Ok(BVF::<I2, N2> {
                data,
                length: bvd.length,
            })
        }
    }
}

impl<I: Integer, const N: usize> TryFrom<&'_ BVD> for BVF<I, N>
where
    u64: StaticCast<I>,
{
    type Error = ConvertError;
    fn try_from(bvd: &'_ BVD) -> Result<Self, Self::Error> {
        if bvd.len() > BVF::<I, N>::capacity() {
            Err(ConvertError::NotEnoughCapacity)
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
    type Error = ConvertError;
    fn try_from(bvd: BVD) -> Result<Self, Self::Error> {
        Self::try_from(&bvd)
    }
}

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

impl<I: Integer, const N: usize> Not for &'_ BVF<I, N> {
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


        impl<I: Integer, const N: usize> ShlAssign<&'_ $rhs> for BVF<I, N> {
            fn shl_assign(&mut self, rhs: &'_ $rhs) {
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

        impl<I: Integer, const N: usize> Shl<&'_ $rhs> for BVF<I, N> {
            type Output = BVF<I, N>;
            fn shl(mut self, rhs: &'_ $rhs) -> Self {
                self.shl_assign(rhs);
                return self;
            }
        }

        impl<I: Integer, const N: usize> Shl<$rhs> for &'_ BVF<I, N> {
            type Output = BVF<I, N>;
            fn shl(self, rhs: $rhs) -> BVF<I, N> {
                return (*self).shl(rhs);
            }
        }

        impl<I: Integer, const N: usize> Shl<&'_ $rhs> for &'_ BVF<I, N> {
            type Output = BVF<I, N>;
            fn shl(self, rhs: &'_ $rhs) -> BVF<I, N> {
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

        impl<I: Integer, const N: usize> ShrAssign<&'_ $rhs> for BVF<I, N> {
            fn shr_assign(&mut self, rhs: &'_ $rhs) {
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

        impl<I: Integer, const N: usize> Shr<&'_ $rhs> for BVF<I, N> {
            type Output = BVF<I, N>;
            fn shr(mut self, rhs: &'_ $rhs) -> Self {
                self.shr_assign(rhs);
                return self;
            }
        }

        impl<I: Integer, const N: usize> Shr<$rhs> for &'_ BVF<I, N> {
            type Output = BVF<I, N>;
            fn shr(self, rhs: $rhs) -> BVF<I, N> {
                return (*self).shr(rhs);
            }
        }

        impl<I: Integer, const N: usize> Shr<&'_ $rhs> for &'_ BVF<I, N> {
            type Output = BVF<I, N>;
            fn shr(self, rhs: &'_ $rhs) -> BVF<I, N> {
                self.shr(*rhs)
            }
        }
    )+
}}

impl_shifts!({u8, u16, u32, u64, u128, usize});

macro_rules! impl_binop_assign {
    ($trait:ident, $method:ident) => {
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
                        self.data[i].$method(IArray::<I1>::get_int(rhs, i).unwrap_or(I1::ZERO));
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
    };
}

impl_binop_assign!(BitAndAssign, bitand_assign);
impl_binop_assign!(BitOrAssign, bitor_assign);
impl_binop_assign!(BitXorAssign, bitxor_assign);

macro_rules! impl_addsub_assign {
    ($trait:ident, $method:ident, $carry_method:ident) => {
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
                        carry = self.data[i].$carry_method(
                            IArray::<I1>::get_int(rhs, i).unwrap_or(I1::ZERO),
                            carry,
                        );
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
    };
}

impl_addsub_assign!(AddAssign, add_assign, carry_add);
impl_addsub_assign!(SubAssign, sub_assign, carry_sub);

macro_rules! impl_op {
    ($trait:ident, $method:ident, $assign_method:ident) => {
        impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> $trait<BVF<I2, N2>>
            for BVF<I1, N1>
        where
            I2: StaticCast<I1>,
        {
            type Output = BVF<I1, N1>;
            fn $method(mut self, rhs: BVF<I2, N2>) -> BVF<I1, N1> {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> $trait<&'_ BVF<I2, N2>>
            for BVF<I1, N1>
        where
            I2: StaticCast<I1>,
        {
            type Output = BVF<I1, N1>;
            fn $method(mut self, rhs: &'_ BVF<I2, N2>) -> BVF<I1, N1> {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> $trait<BVF<I2, N2>>
            for &'_ BVF<I1, N1>
        where
            I2: StaticCast<I1>,
        {
            type Output = BVF<I1, N1>;
            fn $method(self, rhs: BVF<I2, N2>) -> BVF<I1, N1> {
                return (*self).$method(rhs);
            }
        }

        impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> $trait<&'_ BVF<I2, N2>>
            for &'_ BVF<I1, N1>
        where
            I2: StaticCast<I1>,
        {
            type Output = BVF<I1, N1>;
            fn $method(self, rhs: &'_ BVF<I2, N2>) -> BVF<I1, N1> {
                return (*self).$method(rhs);
            }
        }
    };
}

impl_op!(BitAnd, bitand, bitand_assign);
impl_op!(BitOr, bitor, bitor_assign);
impl_op!(BitXor, bitxor, bitxor_assign);
impl_op!(Add, add, add_assign);
impl_op!(Sub, sub, sub_assign);

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Mul<&'_ BVF<I2, N2>>
    for &'_ BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn mul(self, rhs: &'_ BVF<I2, N2>) -> BVF<I1, N1> {
        let mut res = BVF::<I1, N1>::zeros(self.length);
        let len = IArray::<I1>::int_len(&res);
        for i in 0..(len - 1) {
            for j in 0..(i + 1) {
                let c = self.data[i - j]
                    .widening_mul(IArray::<I1>::get_int(rhs, j).unwrap_or(I1::ZERO));
                let carry = res.data[i].carry_add(c.0, I1::ZERO);
                res.data[i + 1].carry_add(c.1, carry);
            }
        }
        for j in 0..len {
            let c = self.data[len - 1 - j]
                .widening_mul(IArray::<I1>::get_int(rhs, j).unwrap_or(I1::ZERO));
            res.data[len - 1].carry_add(c.0, I1::ZERO);
        }

        res.mod2n(self.length);
        res
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Mul<BVF<I2, N2>>
    for &'_ BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn mul(self, rhs: BVF<I2, N2>) -> BVF<I1, N1> {
        self.mul(&rhs)
    }
}

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Mul<&'_ BVF<I2, N2>>
    for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    type Output = BVF<I1, N1>;
    fn mul(self, rhs: &'_ BVF<I2, N2>) -> BVF<I1, N1> {
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

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> MulAssign<&'_ BVF<I2, N2>>
    for BVF<I1, N1>
where
    I2: StaticCast<I1>,
{
    fn mul_assign(&mut self, rhs: &'_ BVF<I2, N2>) {
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

impl<I: Integer, J: Integer, const N: usize> IArray<I> for BVF<J, N>
where
    J: StaticCast<I>,
{
    fn int_len(&self) -> usize {
        (self.length + size_of::<I>() * 8 - 1) / (size_of::<I>() * 8)
    }

    fn get_int(&self, idx: usize) -> Option<I> {
        if idx < IArray::<I>::int_len(self) {
            IArray::<I>::get_int(self.data.as_ref(), idx)
        } else {
            None
        }
    }
}

impl<I: Integer, J: Integer, const N: usize> IArrayMut<I> for BVF<J, N>
where
    J: StaticCast<I>,
{
    fn set_int(&mut self, idx: usize, v: I) -> Option<I> {
        if idx < IArray::<I>::int_len(self) {
            IArrayMut::<I>::set_int(self.data.as_mut(), idx, v)
        } else {
            None
        }
    }
}

impl<'a, I: Integer, const N: usize> IntoIterator for &'a BVF<I, N> {
    type Item = Bit;
    type IntoIter = BitIterator<'a, BVF<I, N>>;

    fn into_iter(self) -> Self::IntoIter {
        BitIterator::new(self)
    }
}
