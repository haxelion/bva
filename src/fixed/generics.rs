use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::iter::repeat;
use std::mem::size_of;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, 
    Div, DivAssign, Mul, MulAssign, Not, Range, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

use crate::{Bit, BitVector, ConvertError, Endianness};
use crate::utils::{Constants, StaticCast};

pub trait Integer : Add<Output=Self> + AddAssign + BitAnd<Output=Self> + BitAndAssign +
    BitOr<Output=Self> + BitOrAssign + BitXor<Output=Self> + BitXorAssign + Constants + Copy + 
    fmt::Debug + Div<Output=Self> + DivAssign + Eq + From<Bit> + Into<Bit> + Mul<Output=Self> +
    MulAssign+ Not<Output=Self> + Ord + PartialEq + PartialOrd + Shl<usize, Output=Self> + 
    ShlAssign<usize> + Shr<usize, Output=Self> + ShrAssign<usize> + Sub<Output=Self> + SubAssign + 
    Sized + StaticCast<u8> {}

impl Integer for u8 {}
impl Integer for u16 {}
impl Integer for u32 {}
impl Integer for u64 {}
impl Integer for u128 {}
impl Integer for usize {}

#[derive(Copy, Clone, Debug)]
pub struct BV<I: Integer, const N: usize> {
    data: [I; N],
    length: usize
}

impl<I: Integer, const N: usize> BV<I, N> {
    const BYTE_UNIT: usize = size_of::<I>();
    const NIBBLE_UNIT: usize = size_of::<I>() * 2;
    const SEMI_NIBBLE_UNIT: usize = size_of::<I>() * 4;
    const BIT_UNIT: usize = size_of::<I>() * 8;

    pub fn capacity() -> usize {
        size_of::<I>() * 8 * N
    }

    fn capacity_from_bit_len(bit_length: usize) -> usize {
        (bit_length + Self::BIT_UNIT - 1) / Self::BIT_UNIT
    }

    fn mask(length: usize) -> I {
        // Re-implementation of checked_shr since we don't have a generic trait for it.
        if length == 0 {
            I::ZERO
        }
        else {
            I::MAX.shr(Self::BIT_UNIT - length)
        }
    }
}

impl<I: Integer, const N: usize> BitVector for BV<I, N> {
    fn zeros(length: usize) -> Self {
        debug_assert!(length <= Self::capacity());
        Self {
            data: [I::ZERO; N],
            length
        }
    }

    fn ones(length: usize) -> Self {
        debug_assert!(length <= Self::capacity());
        let mut data = [I::MAX; N];
        for i in 0..N {
            data[i] &= Self::mask(usize::min(length - usize::min(length, i * Self::BIT_UNIT), Self::BIT_UNIT));
        }
        Self {
            data,
            length
        }
    }

    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertError> {
        let length = string.as_ref().chars().count();
        if length > Self::capacity() {
            return Err(ConvertError::NotEnoughCapacity);
        }

        let offset = (Self::BIT_UNIT - length % Self::BIT_UNIT) % Self::BIT_UNIT;
        let mut data = [I::ZERO; N];

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = data.len() - 1 - (i + offset) / Self::BIT_UNIT;
            data[j] = (data[j] << 1) | match c {
                '0' => I::ZERO,
                '1' => I::ONE,
                _ => return Err(ConvertError::InvalidFormat(i))
            };
        }
        Ok(Self {
            data,
            length
        })
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertError> {
        let length = string.as_ref().chars().count();
        if length * 4 > Self::capacity() {
            return Err(ConvertError::NotEnoughCapacity);
        }

        let offset = (Self::NIBBLE_UNIT - length % Self::NIBBLE_UNIT) % Self::NIBBLE_UNIT;
        let mut data = [I::ZERO; N];

        for (i, c) in string.as_ref().chars().enumerate() {
            let j = data.len() - 1 - (i + offset) / Self::NIBBLE_UNIT;
            data[j] = (data[j] << 4) | match c.to_digit(16) {
                Some(d) => I::cast_from(d as u8),
                None => return Err(ConvertError::InvalidFormat(i))
            };
        }  
        Ok(Self {
            data,
            length: length * 4
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
                let offset = (Self::BYTE_UNIT - byte_length % Self::BYTE_UNIT) % Self::BYTE_UNIT;
                for (i, b) in bytes.as_ref().iter().rev().enumerate() {
                    let j = data.len() - 1 - (i + offset) / Self::BYTE_UNIT;
                    data[j] = (data[j] << 8) | I::cast_from(*b);
                }
            },
            Endianness::BE => {
                let offset = (Self::BYTE_UNIT - byte_length % Self::BYTE_UNIT) % Self::BYTE_UNIT;
                for (i, b) in bytes.as_ref().iter().enumerate() {
                    let j = data.len() - 1 - (i + offset) / Self::BYTE_UNIT;
                    data[j] = (data[j] << 8) | I::cast_from(*b);
                }
            }
        }
        Ok(Self {
            data,
            length: byte_length * 8
        })
    }

    fn to_vec(&self, endianness: Endianness) -> Vec<u8> {
        let num_bytes = (self.length + 7) / 8;
        let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
        match endianness {
            Endianness::LE => {
                for i in 0..num_bytes {
                    buf[i] = (self.data[i / Self::BYTE_UNIT] >> ((i % Self::BYTE_UNIT) * 8)).cast_to();
                }
            },
            Endianness::BE => {
                for i in 0..num_bytes {
                    buf[num_bytes - i - 1] = (self.data[i / Self::BYTE_UNIT] >> ((i % Self::BYTE_UNIT) * 8)).cast_to();
                }
            }
        }
        return buf;
    }

    fn read<R: std::io::Read>(reader: &mut R, length: usize, endianness: Endianness) -> std::io::Result<Self> {
        if length > Self::capacity() {
            return Err(std::io::Error::new(std::io::ErrorKind::InvalidInput, ConvertError::NotEnoughCapacity));
        }
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

    fn write<W: std::io::Write>(&self, writer: &mut W, endianness: Endianness) -> std::io::Result<()> {
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
                data[i] = (self.data[i + offset] >> slide) | 
                    (*self.data.get(i + offset + 1).unwrap_or(&I::ZERO) << (Self::BIT_UNIT - slide));
            }
        }
        else {
            for i in 0..Self::capacity_from_bit_len(length) {
                data[i] = self.data[i + offset];
            }
        }

        if let Some(last) = data.get_mut(Self::capacity_from_bit_len(length)) {
            *last &= Self::mask(length.wrapping_sub(1) % Self::BIT_UNIT + 1);
        }

        BV::<I,N> {
            data,
            length
        }
    }

    fn push(&mut self, bit: Bit) {
        debug_assert!(self.length < Self::capacity());
        self.set(self.length, bit);
        self.length += 1;
    }

    fn pop(&mut self) -> Option<Bit> {
        if self.length > 0 {
            self.length -= 1;
            Some(self.get(self.length))
        }
        else {
            None
        }
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
        }
        else if new_length > self.length {
            debug_assert!(new_length <= Self::capacity());
            let sign_pattern = match bit {
                Bit::Zero => I::MIN,
                Bit::One  => I::MAX,
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
            self.data[i] = (self.data[i] << 1 | carry.into()) & Self::mask(self.length % Self::BIT_UNIT);
            carry = b.into();
        }
        return carry;
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
        return carry;
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
            new_data[new_idx / Self::BIT_UNIT] |= ((self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & Self::mask(l)) << (new_idx % Self::BIT_UNIT);
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
            new_data[new_idx / Self::BIT_UNIT] |= ((self.data[old_idx / Self::BIT_UNIT] >> (old_idx % Self::BIT_UNIT)) & Self::mask(l)) << (new_idx % Self::BIT_UNIT);
            new_idx += l;
        }
        self.data = new_data;
    }

    fn len(&self) -> usize {
        self.length
    }
}

impl<I: Integer, const N: usize> PartialEq for BV<I, N> {
    fn eq(&self, other: &Self) -> bool {
        for i in 0..N {
            if self.data.get(i).unwrap_or(&I::ZERO) != other.data.get(i).unwrap_or(&I::ZERO) {
                return false;
            }
        }
        return true;
    }
}

impl<I: Integer, const N: usize> Eq for BV<I, N> {}


impl<I: Integer, const N: usize> Ord for BV<I, N> {
    fn cmp(&self, other: &Self) -> Ordering { 
        for i in (0..N).rev() {
            match self.data.get(i).unwrap_or(&I::ZERO).cmp(other.data.get(i).unwrap_or(&I::ZERO)) {
                Ordering::Equal => continue,
                ord => return ord
            }
        }
        return Ordering::Equal;
    }
}

impl<I: Integer, const N: usize> PartialOrd for BV<I, N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: Integer, const N: usize> fmt::Binary for BV<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

impl<I: Integer, const N: usize> fmt::Display for BV<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: waiting for div and mod operations
        todo!()
    }
}

impl<I: Integer, const N: usize> fmt::Octal for BV<I, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const SEMI_NIBBLE: [char;8] = ['0', '1', '2', '3', '4', '5', '6', '7'];
        let length = (self.length + 2) / 3;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            let semi_nibble = (self.data[i / Self::NIBBLE_UNIT] >> ((i % Self::NIBBLE_UNIT) * 4)).cast_to() & 0x7;
            s.push(SEMI_NIBBLE[semi_nibble as usize]);
        }
        if f.alternate() {
            return write!(f, "0x{}", s.as_str());
        }
        else {
            return write!(f, "{}", s.as_str());
        }
    }
}

impl<I: Integer, const N: usize> fmt::LowerHex for BV<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const NIBBLE: [char;16] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'];
        let length = (self.length + 3) / 4;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            let nibble = (self.data[i / Self::NIBBLE_UNIT] >> ((i % Self::NIBBLE_UNIT) * 4)).cast_to() & 0xf;
            s.push(NIBBLE[nibble as usize]);
        }
        if f.alternate() {
            return write!(f, "0x{}", s.as_str());
        }
        else {
            return write!(f, "{}", s.as_str());
        }
    }
}

impl<I: Integer, const N: usize> fmt::UpperHex for BV<I, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const NIBBLE: [char;16] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'];
        let length = (self.length + 3) / 4;
        let mut s = String::with_capacity(length);
        for i in (0..length).rev() {
            let nibble = (self.data[i / Self::NIBBLE_UNIT] >> ((i % Self::NIBBLE_UNIT) * 4)).cast_to() & 0xf;
            s.push(NIBBLE[nibble as usize]);
        }
        if f.alternate() {
            return write!(f, "0x{}", s.as_str());
        }
        else {
            return write!(f, "{}", s.as_str());
        }
    }
}

macro_rules! impl_tryfrom { ($($type:ty),+) => {
    $(
        impl<I: Integer, const N: usize> TryFrom<$type> for BV<I, N>
            where I: StaticCast<$type>
        {
            type Error = ConvertError;

            fn try_from(int: $type) -> Result<Self, Self::Error> {
                // Branch should be optimized at compile time
                if size_of::<I>() >= size_of::<$type>() {
                    let mut data = [I::ZERO; N];
                    data[0] = I::cast_from(int);
                    return Ok(BV {
                        data,
                        length: size_of::<$type>() * 8
                    });
                }
                else {
                    // Check if value overflow the bit vector
                    if int.shr(Self::capacity()) != 0 {
                        return Err(ConvertError::NotEnoughCapacity);
                    }
                    let mut data = [I::ZERO; N];
                    for i in 0..N {
                        data[i] = I::cast_from(int.shr(i * Self::BIT_UNIT));
                    }
                    return Ok(BV {
                        data,
                        length: Self::capacity()
                    });
                }
            }
        }

        impl<I: Integer, const N: usize> TryFrom<BV<I, N>> for $type
            where $type: StaticCast<I>
        {
            type Error = ConvertError;

            fn try_from(bv: BV<I, N>) -> Result<Self, Self::Error> {
                // Check if the bit vector overflow I
                if bv.len() > size_of::<$type>() * 8 {
                    return Err(ConvertError::NotEnoughCapacity);
                }
                if size_of::<I>() >= size_of::<$type>() {
                    return Ok(<$type>::cast_from(bv.data[0]));
                }
                else {
                    let mut value = 0;
                    for i in 0..N {
                        value &= <$type>::cast_from(bv.data[i]).shl(i * BV::<I, N>::BIT_UNIT);
                    }
                    return Ok(value);
                }
            }
        }
    )+
}}

impl_tryfrom!(u8, u16, u32, u64, u128, usize);

impl<I1: Integer, I2: Integer, const N1: usize, const N2: usize> Add<BV<I2, N2>> for BV<I1, N1> 
    where I1: StaticCast<I2>,
{
    type Output = BV<I1, N1>;

    fn add(self, rhs: BV<I2, N2>) -> Self::Output {
        // Branch should be optimized at compile time
        if size_of::<I1>() < size_of::<I2>() {
            let f = size_of::<I2>() / size_of::<I1>();
            let mut res = self.data;
            for i in 0..usize::min(N1, N2*f) {
                res[i].add_assign(I1::cast_from(rhs.data[i / f].shl((i & f) * size_of::<I1>() * 8)));
            }
            BV {
                data: res,
                length: self.length
            }
        }
        else if size_of::<I1>() > size_of::<I2>() {
            let f = size_of::<I1>() / size_of::<I2>();
            let mut res = self.data;
            for i in 0..usize::min(N1*f, N2) {
                res[i/f].add_assign(I1::cast_from(rhs.data[i]).shr((i & f) * size_of::<I2>() * 8));
            }
            BV {
                data: res,
                length: self.length
            }
        }
        else { // size_of::<I1>() == size_of::<I2>()
            let mut res = self.data;
            for i in 0..usize::min(N1, N2) {
                res[i].add_assign(I1::cast_from(rhs.data[i]));
            }
            BV {
                data: res,
                length: self.length
            }
        }
    }
}