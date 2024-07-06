//! This module contains an automatically managed bit vector type. Depending on the required
//! capacity, it might use a fixed capacity implementation to avoid unnecessary dynamic memory
//! allocations, or it might use a dynamic capacity implementation if the capacity of fixed
//! implementations is exceeded.
//!
//! While avoiding memory allocation might improve performance, there is a slight performance cost
//! due to the dynamic dispatch and extra capacity checks. The net effect will depend on the exact
//! application. It is designed for the case where most bit vector are expected to fit inside
//! fixed capacity implementations but some outliers might not.

use std::cmp::Ordering;
use std::fmt::{Binary, Display, LowerHex, Octal, UpperHex};

use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Mul, MulAssign,
    Not, Range, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::dynamic::BVD;
#[allow(unused_imports)]
use crate::fixed::{BV128, BV16, BV32, BV64, BV8, BVF};
use crate::iter::BitIterator;
use crate::utils::{IArray, IArrayMut, Integer, StaticCast};
use crate::Bit;
use crate::{BitVector, ConvertionError, Endianness};

// Choose a fixed BVF type which should match the size of BVD inside the enum
#[cfg(target_pointer_width = "16")]
type BVP = BV32;
#[cfg(target_pointer_width = "32")]
type BVP = BV64;
#[cfg(target_pointer_width = "64")]
type BVP = BV128;

// ------------------------------------------------------------------------------------------------
// Bit Vector automatic allocation implementation
// ------------------------------------------------------------------------------------------------

/// A bit vector with automatic capacity management.
#[derive(Clone, Debug)]
pub enum BV {
    Fixed(BVP),
    Dynamic(BVD),
}

impl BV {
    /// Reserve will reserve room for at least `additional` bits in the bit vector. The actual
    /// length of the bit vector will stay unchanged, see [`BitVector::resize`] to change the actual
    /// length of the bit vector.
    ///
    /// Calling this method might cause the storage to become dynamically allocated.
    pub fn reserve(&mut self, additional: usize) {
        match self {
            &mut BV::Fixed(ref b) => {
                if b.len() + additional > BVP::capacity() {
                    let mut new_b = BVD::from(b);
                    new_b.reserve(additional);
                    *self = BV::Dynamic(new_b);
                }
            }
            BV::Dynamic(b) => b.reserve(additional),
        }
    }

    /// Drop as much excess capacity as possible in the bit vector to fit the current length.
    ///
    /// Calling this method might cause the implementation to drop unnecessary dynamically
    /// allocated memory.
    pub fn shrink_to_fit(&mut self) {
        if let BV::Dynamic(b) = self {
            if b.len() <= BVP::capacity() {
                let new_b = BVP::try_from(&*b).unwrap();
                *self = BV::Fixed(new_b);
            } else {
                b.shrink_to_fit();
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BV - Integer Array traits
// ------------------------------------------------------------------------------------------------

impl<I: Integer> IArray<I> for BV
where
    u64: StaticCast<I>,
{
    fn int_len(&self) -> usize {
        match self {
            BV::Fixed(bvf) => IArray::<I>::int_len(bvf),
            BV::Dynamic(bvd) => IArray::<I>::int_len(bvd),
        }
    }

    fn get_int(&self, idx: usize) -> Option<I> {
        match self {
            BV::Fixed(bvf) => IArray::<I>::get_int(bvf, idx),
            BV::Dynamic(bvd) => IArray::<I>::get_int(bvd, idx),
        }
    }
}

impl<I: Integer> IArrayMut<I> for BV
where
    u64: StaticCast<I>,
{
    fn set_int(&mut self, idx: usize, v: I) -> Option<I> {
        match self {
            BV::Fixed(bvf) => IArrayMut::<I>::set_int(bvf, idx, v),
            BV::Dynamic(bvd) => IArrayMut::<I>::set_int(bvd, idx, v),
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BV - Bit Vector core trait
// ------------------------------------------------------------------------------------------------

impl BitVector for BV {
    fn with_capacity(capacity: usize) -> Self {
        if capacity <= BVP::capacity() {
            BV::Fixed(BVP::with_capacity(capacity))
        } else {
            BV::Dynamic(BVD::with_capacity(capacity))
        }
    }

    fn zeros(length: usize) -> Self {
        if length <= BVP::capacity() {
            BV::Fixed(BVP::zeros(length))
        } else {
            BV::Dynamic(BVD::zeros(length))
        }
    }

    fn ones(length: usize) -> Self {
        if length <= BVP::capacity() {
            BV::Fixed(BVP::ones(length))
        } else {
            BV::Dynamic(BVD::ones(length))
        }
    }

    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError> {
        if string.as_ref().len() <= BVP::capacity() {
            Ok(BV::Fixed(BVP::from_binary(string)?))
        } else {
            Ok(BV::Dynamic(BVD::from_binary(string)?))
        }
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError> {
        if string.as_ref().len() * 4 <= BVP::capacity() {
            Ok(BV::Fixed(BVP::from_hex(string)?))
        } else {
            Ok(BV::Dynamic(BVD::from_hex(string)?))
        }
    }

    fn from_bytes<B: AsRef<[u8]>>(
        bytes: B,
        endianness: Endianness,
    ) -> Result<Self, ConvertionError> {
        if bytes.as_ref().len() * 8 <= BVP::capacity() {
            Ok(BV::Fixed(BVP::from_bytes(bytes, endianness)?))
        } else {
            Ok(BV::Dynamic(BVD::from_bytes(bytes, endianness)?))
        }
    }

    fn to_vec(&self, endianness: Endianness) -> Vec<u8> {
        match self {
            BV::Fixed(b) => b.to_vec(endianness),
            BV::Dynamic(b) => b.to_vec(endianness),
        }
    }

    fn read<R: std::io::Read>(
        reader: &mut R,
        length: usize,
        endianness: Endianness,
    ) -> std::io::Result<Self> {
        if length <= BVP::capacity() {
            Ok(BV::Fixed(BVP::read(reader, length, endianness)?))
        } else {
            Ok(BV::Dynamic(BVD::read(reader, length, endianness)?))
        }
    }

    fn write<W: std::io::Write>(
        &self,
        writer: &mut W,
        endianness: Endianness,
    ) -> std::io::Result<()> {
        match self {
            BV::Fixed(b) => b.write(writer, endianness),
            BV::Dynamic(b) => b.write(writer, endianness),
        }
    }

    fn get(&self, index: usize) -> Bit {
        match self {
            BV::Fixed(b) => b.get(index),
            BV::Dynamic(b) => b.get(index),
        }
    }

    fn set(&mut self, index: usize, bit: Bit) {
        match self {
            BV::Fixed(b) => b.set(index, bit),
            BV::Dynamic(b) => b.set(index, bit),
        }
    }

    fn copy_range(&self, range: Range<usize>) -> Self {
        match self {
            BV::Fixed(b) => BV::Fixed(b.copy_range(range)),
            BV::Dynamic(b) => {
                let s = b.copy_range(range);
                if s.len() <= BVP::capacity() {
                    BV::Fixed(BVP::try_from(s).unwrap())
                } else {
                    BV::Dynamic(s)
                }
            }
        }
    }

    fn push(&mut self, bit: Bit) {
        self.reserve(1);
        match self {
            BV::Fixed(b) => b.push(bit),
            BV::Dynamic(b) => b.push(bit),
        }
    }

    fn pop(&mut self) -> Option<Bit> {
        match self {
            BV::Fixed(b) => b.pop(),
            BV::Dynamic(b) => b.pop(),
        }
    }

    fn resize(&mut self, new_length: usize, bit: Bit) {
        if new_length > self.len() {
            self.reserve(new_length - self.len());
        }
        match self {
            BV::Fixed(b) => b.resize(new_length, bit),
            BV::Dynamic(b) => b.resize(new_length, bit),
        }
    }

    fn shl_in(&mut self, bit: Bit) -> Bit {
        match self {
            BV::Fixed(b) => b.shl_in(bit),
            BV::Dynamic(b) => b.shl_in(bit),
        }
    }

    fn shr_in(&mut self, bit: Bit) -> Bit {
        match self {
            BV::Fixed(b) => b.shr_in(bit),
            BV::Dynamic(b) => b.shr_in(bit),
        }
    }

    fn rotl(&mut self, rot: usize) {
        match self {
            BV::Fixed(b) => b.rotl(rot),
            BV::Dynamic(b) => b.rotl(rot),
        }
    }

    fn rotr(&mut self, rot: usize) {
        match self {
            BV::Fixed(b) => b.rotr(rot),
            BV::Dynamic(b) => b.rotr(rot),
        }
    }

    fn capacity(&self) -> usize {
        match self {
            BV::Fixed(_) => BVP::capacity(),
            BV::Dynamic(b) => b.capacity(),
        }
    }

    fn len(&self) -> usize {
        match self {
            BV::Fixed(b) => b.len(),
            BV::Dynamic(b) => b.len(),
        }
    }

    fn iter(&self) -> BitIterator<'_, Self> {
        self.into_iter()
    }

    fn leading_zeros(&self) -> usize {
        match self {
            BV::Fixed(b) => b.leading_zeros(),
            BV::Dynamic(b) => b.leading_zeros(),
        }
    }

    fn leading_ones(&self) -> usize {
        match self {
            BV::Fixed(b) => b.leading_ones(),
            BV::Dynamic(b) => b.leading_ones(),
        }
    }

    fn trailing_zeros(&self) -> usize {
        match self {
            BV::Fixed(b) => b.trailing_zeros(),
            BV::Dynamic(b) => b.trailing_zeros(),
        }
    }

    fn trailing_ones(&self) -> usize {
        match self {
            BV::Fixed(b) => b.trailing_ones(),
            BV::Dynamic(b) => b.trailing_ones(),
        }
    }

    fn is_zero(&self) -> bool {
        match self {
            BV::Fixed(b) => b.is_zero(),
            BV::Dynamic(b) => b.is_zero(),
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BV - Bit iterator trait
// ------------------------------------------------------------------------------------------------

impl<'a> IntoIterator for &'a BV {
    type Item = Bit;
    type IntoIter = BitIterator<'a, BV>;

    fn into_iter(self) -> Self::IntoIter {
        BitIterator::new(self)
    }
}

impl FromIterator<Bit> for BV {
    fn from_iter<T: IntoIterator<Item = Bit>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut bv = BV::with_capacity(iter.size_hint().0);
        iter.for_each(|b| bv.push(b));
        bv
    }
}

// ------------------------------------------------------------------------------------------------
// BV - Formatting traits
// ------------------------------------------------------------------------------------------------

impl Binary for BV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BV::Fixed(b) => Binary::fmt(b, f),
            BV::Dynamic(b) => Binary::fmt(b, f),
        }
    }
}

/// TODO: this implementation is broken for bit vector longer than 128 bits.
impl Display for BV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BV::Fixed(b) => Display::fmt(b, f),
            BV::Dynamic(b) => Display::fmt(b, f),
        }
    }
}

impl LowerHex for BV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BV::Fixed(b) => LowerHex::fmt(b, f),
            BV::Dynamic(b) => LowerHex::fmt(b, f),
        }
    }
}

impl UpperHex for BV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BV::Fixed(b) => UpperHex::fmt(b, f),
            BV::Dynamic(b) => UpperHex::fmt(b, f),
        }
    }
}

impl Octal for BV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BV::Fixed(b) => Octal::fmt(b, f),
            BV::Dynamic(b) => Octal::fmt(b, f),
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BV - Comparison traits
// ------------------------------------------------------------------------------------------------

impl PartialEq for BV {
    fn eq(&self, other: &Self) -> bool {
        match self {
            BV::Fixed(b1) => match other {
                BV::Fixed(b2) => b1.eq(b2),
                BV::Dynamic(b2) => b1.eq(b2),
            },
            BV::Dynamic(b1) => match other {
                BV::Fixed(b2) => b1.eq(b2),
                BV::Dynamic(b2) => b1.eq(b2),
            },
        }
    }
}

impl PartialEq<BVD> for BV {
    fn eq(&self, other: &BVD) -> bool {
        match self {
            BV::Fixed(bvf) => bvf.eq(other),
            BV::Dynamic(bvd) => bvd.eq(other),
        }
    }
}

impl<I: Integer, const N: usize> PartialEq<BVF<I, N>> for BV
where
    u64: StaticCast<I>,
{
    fn eq(&self, other: &BVF<I, N>) -> bool {
        match self {
            BV::Fixed(bvf) => bvf.eq(other),
            BV::Dynamic(bvd) => bvd.eq(other),
        }
    }
}

impl Eq for BV {}

impl PartialOrd for BV {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: Integer, const N: usize> PartialOrd<BVF<I, N>> for BV
where
    u64: StaticCast<I>,
{
    fn partial_cmp(&self, other: &BVF<I, N>) -> Option<Ordering> {
        match self {
            BV::Fixed(bvf) => bvf.partial_cmp(other).map(|o| o.reverse()),
            BV::Dynamic(bvd) => bvd.partial_cmp(other).map(|o| o.reverse()),
        }
    }
}

impl PartialOrd<BVD> for BV {
    fn partial_cmp(&self, other: &BVD) -> Option<Ordering> {
        match self {
            BV::Fixed(bvf) => bvf.partial_cmp(other).map(|o| o.reverse()),
            BV::Dynamic(bvd) => bvd.partial_cmp(other).map(|o| o.reverse()),
        }
    }
}

impl Ord for BV {
    fn cmp(&self, other: &Self) -> Ordering {
        match self {
            BV::Fixed(b1) => match other {
                BV::Fixed(b2) => b1.cmp(b2),
                BV::Dynamic(b2) => b1.partial_cmp(b2).unwrap(),
            },
            BV::Dynamic(b1) => match other {
                BV::Fixed(b2) => b1.partial_cmp(b2).unwrap(),
                BV::Dynamic(b2) => b1.cmp(b2),
            },
        }
    }
}

// ------------------------------------------------------------------------------------------------
// BV - Conversion traits
// ------------------------------------------------------------------------------------------------

impl From<BVD> for BV {
    fn from(b: BVD) -> Self {
        if let Ok(bvf) = BVP::try_from(&b) {
            BV::Fixed(bvf)
        } else {
            BV::Dynamic(b)
        }
    }
}

impl From<&'_ BVD> for BV {
    fn from(b: &'_ BVD) -> Self {
        if let Ok(bvf) = BVP::try_from(b) {
            BV::Fixed(bvf)
        } else {
            BV::Dynamic(b.clone())
        }
    }
}

impl<I: Integer, const N: usize> From<&BVF<I, N>> for BV {
    fn from(b: &BVF<I, N>) -> Self {
        if BVF::<I, N>::capacity() <= BVP::capacity() {
            BV::Fixed(b.try_into().unwrap())
        } else {
            BV::Dynamic(b.into())
        }
    }
}

impl<I: Integer, const N: usize> From<BVF<I, N>> for BV {
    fn from(b: BVF<I, N>) -> Self {
        BV::from(&b)
    }
}

macro_rules! impl_tryfrom { ($($type:ty),+) => {
    $(
        impl From<$type> for BV {
            fn from(int: $type) -> Self {
                // Branch should be optimized at compile time
                if std::mem::size_of::<$type>() * 8 <= BVP::capacity() {
                    BV::Fixed(BVP::try_from(int).unwrap())
                }
                else {
                    BV::Dynamic(BVD::from(int))
                }
            }
        }

        impl TryFrom<&BV> for $type
        {
            type Error = ConvertionError;
            fn try_from(bv: &BV) -> Result<Self, Self::Error> {
                match bv {
                    BV::Fixed(b) => Ok(b.try_into()?),
                    BV::Dynamic(b) => Ok(b.try_into()?),
                }
            }
        }

        impl TryFrom<BV> for $type
        {
            type Error = ConvertionError;
            fn try_from(bv: BV) -> Result<Self, Self::Error> {
                Self::try_from(&bv)
            }
        }
    )+
}}

impl_tryfrom!(u8, u16, u32, u64, u128, usize);

// ------------------------------------------------------------------------------------------------
// BV - Unary operator & shifts
// ------------------------------------------------------------------------------------------------

impl Not for BV {
    type Output = BV;

    fn not(self) -> Self::Output {
        match self {
            BV::Fixed(b) => BV::Fixed(b.not()),
            BV::Dynamic(b) => BV::Dynamic(b.not()),
        }
    }
}

impl Not for &'_ BV {
    type Output = BV;

    fn not(self) -> Self::Output {
        match self {
            BV::Fixed(b) => BV::Fixed(b.not()),
            BV::Dynamic(b) => BV::Dynamic(b.not()),
        }
    }
}

macro_rules! impl_shift_assign {($trait:ident, $method:ident, {$($rhs:ty),+}) => {
    $(
        impl $trait<$rhs> for BV {
            fn $method(&mut self, rhs: $rhs) {
                match self {
                    BV::Fixed(b) => b.$method(rhs),
                    BV::Dynamic(b) => b.$method(rhs)
                }
            }
        }

        impl $trait<&'_ $rhs> for BV {
            fn $method(&mut self, rhs: &'_ $rhs) {
                match self {
                    BV::Fixed(b) => b.$method(rhs),
                    BV::Dynamic(b) => b.$method(rhs)
                }
            }
        }
    )+
}}

impl_shift_assign!(ShlAssign, shl_assign, {u8, u16, u32, u64, u128, usize});
impl_shift_assign!(ShrAssign, shr_assign, {u8, u16, u32, u64, u128, usize});

macro_rules! impl_shift {($trait:ident, $method:ident, {$($rhs:ty),+}) => {
    $(
        impl $trait<$rhs> for BV {
            type Output = BV;
            fn $method(self, rhs: $rhs) -> BV {
                match self {
                    BV::Fixed(b) => BV::Fixed(b.$method(rhs)),
                    BV::Dynamic(b) => BV::Dynamic(b.$method(rhs))
                }
            }
        }

        impl $trait<&'_ $rhs> for BV {
            type Output = BV;
            fn $method(self, rhs: &'_ $rhs) -> BV {
                match self {
                    BV::Fixed(b) => BV::Fixed(b.$method(rhs)),
                    BV::Dynamic(b) => BV::Dynamic(b.$method(rhs))
                }
            }
        }

        impl $trait<$rhs> for &'_ BV {
            type Output = BV;
            fn $method(self, rhs: $rhs) -> BV {
                self.clone().$method(rhs)
            }
        }

        impl $trait<&'_ $rhs> for &'_ BV {
            type Output = BV;
            fn $method(self, rhs: &'_ $rhs) -> BV {
                self.clone().$method(rhs)
            }
        }
    )+
}}

impl_shift!(Shl, shl, {u8, u16, u32, u64, u128, usize});
impl_shift!(Shr, shr, {u8, u16, u32, u64, u128, usize});

// ------------------------------------------------------------------------------------------------
// BV - Arithmetic operators (assignment kind)
// ------------------------------------------------------------------------------------------------

macro_rules! impl_op_assign {
    ($trait:ident, $method:ident) => {
        impl $trait<&BV> for BV {
            fn $method(&mut self, bv: &BV) {
                match bv {
                    BV::Fixed(b) => self.$method(b),
                    BV::Dynamic(b) => self.$method(b),
                }
            }
        }

        impl $trait<BV> for BV {
            fn $method(&mut self, bv: BV) {
                match bv {
                    BV::Fixed(b) => self.$method(b),
                    BV::Dynamic(b) => self.$method(b),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<&BVF<I, N>> for BV {
            fn $method(&mut self, bvf: &BVF<I, N>) {
                match self {
                    BV::Fixed(b) => b.$method(bvf),
                    BV::Dynamic(b) => b.$method(bvf),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<BVF<I, N>> for BV {
            fn $method(&mut self, bvf: BVF<I, N>) {
                match self {
                    BV::Fixed(b) => b.$method(bvf),
                    BV::Dynamic(b) => b.$method(bvf),
                }
            }
        }

        impl $trait<BVD> for BV {
            fn $method(&mut self, bvd: BVD) {
                match self {
                    BV::Fixed(b) => b.$method(bvd),
                    BV::Dynamic(b) => b.$method(bvd),
                }
            }
        }

        impl $trait<&BVD> for BV {
            fn $method(&mut self, bvd: &BVD) {
                match self {
                    BV::Fixed(b) => b.$method(bvd),
                    BV::Dynamic(b) => b.$method(bvd),
                }
            }
        }
    };
}

impl_op_assign!(BitAndAssign, bitand_assign);
impl_op_assign!(BitOrAssign, bitor_assign);
impl_op_assign!(BitXorAssign, bitxor_assign);
impl_op_assign!(AddAssign, add_assign);
impl_op_assign!(SubAssign, sub_assign);
impl_op_assign!(MulAssign, mul_assign);

macro_rules! impl_op {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl<T> $trait<T> for BV
        where
            BV: $assign_trait<T>,
        {
            type Output = BV;
            fn $method(mut self, rhs: T) -> BV {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl<T> $trait<T> for &BV
        where
            BV: $assign_trait<T>,
        {
            type Output = BV;
            fn $method(self, rhs: T) -> BV {
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
impl_op!(Mul, mul, MulAssign, mul_assign);
