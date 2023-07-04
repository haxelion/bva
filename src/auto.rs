//! This module contains an automatically managed bit vector type. Depending on the required
//! capacity, it might use a fixed capacity implementation to avoid unnecessary dynamic memory
//! allocations, or it might use a dynamic capacity implementation if the capacity of fixed
//! implementations is exceeded.
//!
//! While avoiding memory allocation might improve performance, there is a slight performance cost
//! due to the dynamic dispatch and extra capacity checks. The net effect will depend on the exact
//! application. It is designed for the case where most bit vector are expected to fit inside
//! fixed capacity implementations but some outliers might not.

use std::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use std::convert::{From, TryFrom};
use std::fmt::{Binary, Display, LowerHex, Octal, UpperHex};

use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Range,
    Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::dynamic::BVN;
#[allow(unused_imports)]
use crate::fixed::{BV128, BV16, BV32, BV64, BV8};
use crate::iter::BitIterator;
use crate::Bit;
use crate::{BitVector, ConvertError, Endianness};

// Choose a fixed BV type which should match the size of BVN inside the enum
#[cfg(target_pointer_width = "16")]
type BVF = BV32;
#[cfg(target_pointer_width = "32")]
type BVF = BV64;
#[cfg(target_pointer_width = "64")]
type BVF = BV128;

/// A bit vector with automatic capacity management.
#[derive(Clone, Debug)]
pub enum BV {
    Fixed(BVF),
    Dynamic(BVN),
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
                if b.len() + additional > BVF::capacity() {
                    let mut new_b = BVN::from(b);
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
            if b.len() <= BVF::capacity() {
                let new_b = BVF::try_from(&*b).unwrap();
                *self = BV::Fixed(new_b);
            } else {
                b.shrink_to_fit();
            }
        }
    }
}

impl BitVector for BV {
    fn with_capacity(capacity: usize) -> Self {
        if capacity <= BVF::capacity() {
            BV::with_capacity(capacity)
        } else {
            BV::Dynamic(BVN::with_capacity(capacity))
        }
    }

    fn zeros(length: usize) -> Self {
        if length <= BVF::capacity() {
            BV::Fixed(BVF::zeros(length))
        } else {
            BV::Dynamic(BVN::zeros(length))
        }
    }

    fn ones(length: usize) -> Self {
        if length <= BVF::capacity() {
            BV::Fixed(BVF::ones(length))
        } else {
            BV::Dynamic(BVN::ones(length))
        }
    }

    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertError> {
        if string.as_ref().len() <= BVF::capacity() {
            Ok(BV::Fixed(BVF::from_binary(string)?))
        } else {
            Ok(BV::Dynamic(BVN::from_binary(string)?))
        }
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertError> {
        if string.as_ref().len() * 4 <= BVF::capacity() {
            Ok(BV::Fixed(BVF::from_hex(string)?))
        } else {
            Ok(BV::Dynamic(BVN::from_hex(string)?))
        }
    }

    fn from_bytes<B: AsRef<[u8]>>(bytes: B, endianness: Endianness) -> Result<Self, ConvertError> {
        if bytes.as_ref().len() * 8 <= BVF::capacity() {
            Ok(BV::Fixed(BVF::from_bytes(bytes, endianness)?))
        } else {
            Ok(BV::Dynamic(BVN::from_bytes(bytes, endianness)?))
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
        if length <= BVF::capacity() {
            Ok(BV::Fixed(BVF::read(reader, length, endianness)?))
        } else {
            Ok(BV::Dynamic(BVN::read(reader, length, endianness)?))
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

    fn copy_slice(&self, range: Range<usize>) -> Self {
        match self {
            BV::Fixed(b) => BV::Fixed(b.copy_slice(range)),
            BV::Dynamic(b) => {
                let s = b.copy_slice(range);
                if s.len() <= BVF::capacity() {
                    BV::Fixed(BVF::try_from(s).unwrap())
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

    fn len(&self) -> usize {
        match self {
            BV::Fixed(b) => b.len(),
            BV::Dynamic(b) => b.len(),
        }
    }

    fn iter(&self) -> BitIterator<'_, Self> {
        self.into_iter()
    }
}

impl Binary for BV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BV::Fixed(b) => Binary::fmt(b, f),
            BV::Dynamic(b) => Binary::fmt(b, f),
        }
    }
}

/// Warning: this implementation is broken for bit vector longer than 128 bits.
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

impl Eq for BV {}

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

impl PartialOrd for BV {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! impl_eq { ({$($rhs:ty),+}) => {
    $(
        impl PartialEq<$rhs> for BV {
            fn eq(&self, other: &$rhs) -> bool {
                match self {
                    BV::Fixed(b) => b.eq(other),
                    BV::Dynamic(b) => b.eq(other),
                }
            }
        }

        impl PartialEq<BV> for $rhs {
            fn eq(&self, other: &BV) -> bool {
                match other {
                    BV::Fixed(b) => self.eq(b),
                    BV::Dynamic(b) => self.eq(b),
                }
            }
        }
    )+
}}

macro_rules! impl_ord { ({$($rhs:ty),+}) => {
    $(
        impl PartialOrd<$rhs> for BV {
            fn partial_cmp(&self, other: &$rhs) -> Option<Ordering> {
                match self {
                    BV::Fixed(b) => b.partial_cmp(other),
                    BV::Dynamic(b) => b.partial_cmp(other),
                }
            }
        }

        impl PartialOrd<BV> for $rhs {
            fn partial_cmp(&self, other: &BV) -> Option<Ordering> {
                match other {
                    BV::Fixed(b) => self.partial_cmp(b),
                    BV::Dynamic(b) => self.partial_cmp(b),
                }
            }
        }
    )+
}}

impl_eq!({BV8, BV16, BV32, BV64, BV128, BVN});
impl_ord!({BV8, BV16, BV32, BV64, BV128, BVN});

impl From<BVN> for BV {
    fn from(b: BVN) -> Self {
        if let Ok(bvf) = BVF::try_from(&b) {
            BV::Fixed(bvf)
        } else {
            BV::Dynamic(b)
        }
    }
}

impl From<&'_ BVN> for BV {
    fn from(b: &'_ BVN) -> Self {
        if let Ok(bvf) = BVF::try_from(b) {
            BV::Fixed(bvf)
        } else {
            BV::Dynamic(b.clone())
        }
    }
}

impl From<&'_ BV> for BVN {
    fn from(bv: &'_ BV) -> Self {
        match bv {
            BV::Fixed(b) => BVN::from(b),
            BV::Dynamic(b) => b.clone(),
        }
    }
}

impl From<BV> for BVN {
    fn from(bv: BV) -> Self {
        match bv {
            BV::Fixed(b) => BVN::from(b),
            BV::Dynamic(b) => b,
        }
    }
}

macro_rules! impl_froms {({$(($sbv:ty, $sst:ty)),+}, {$(($ubv:ty, $ust:ty)),+}) => {
    $(
        impl From<$sst> for BV {
            fn from(sst: $sst) -> Self {
                if <$sst>::BITS as usize <= BVF::capacity() {
                    // Call should never fail because we check for capacity
                    BV::Fixed(BVF::try_from(sst).unwrap())
                }
                else {
                    BV::Dynamic(BVN::try_from(sst).unwrap())
                }
            }
        }

        impl From<&'_ $sbv> for BV {
            fn from(b: &'_ $sbv) -> Self {
                // Call should never fail because we check for capacity
                if <$sbv>::capacity() <= BVF::capacity() {
                    BV::Fixed(BVF::try_from(b).unwrap())
                }
                else {
                    BV::Dynamic(BVN::try_from(b).unwrap())
                }
            }
        }

        impl From<$sbv> for BV {
            fn from(b: $sbv) -> Self {
                if <$sbv>::capacity() <= BVF::capacity() {
                    // Call should never fail because we check for capacity
                    BV::Fixed(BVF::try_from(&b).unwrap())
                }
                else {
                    BV::Dynamic(BVN::from(b))
                }
            }
        }

        impl TryFrom<&'_ BV> for $sst {
            type Error = ConvertError;
            fn try_from(bv: &'_ BV) -> Result<Self, Self::Error> {
                match bv {
                    BV::Fixed(b) => <$sst>::try_from(b),
                    BV::Dynamic(b) => <$sst>::try_from(b),
                }
            }
        }

        impl TryFrom<BV> for $sst {
            type Error = ConvertError;
            fn try_from(bv: BV) -> Result<Self, Self::Error> {
                <$sst>::try_from(&bv)
            }
        }

        impl TryFrom<&'_ BV> for $sbv {
            type Error = ConvertError;
            fn try_from(bv: &'_ BV) -> Result<Self, Self::Error> {
                match bv {
                    BV::Fixed(b) => <$sbv>::try_from(b),
                    BV::Dynamic(b) => <$sbv>::try_from(b),
                }
            }
        }

        impl TryFrom<BV> for $sbv {
            type Error = ConvertError;
            fn try_from(bv: BV) -> Result<Self, Self::Error> {
                <$sbv>::try_from(&bv)
            }
        }
    )+

    $(
        impl From<$ust> for BV {
            fn from(ust: $ust) -> Self {
                BV::Dynamic(BVN::from(ust))
            }
        }

        impl From<&'_ $ubv> for BV {
            fn from(ubv: &'_ $ubv) -> Self {
                if ubv.len() <= BVF::capacity() {
                    BV::Fixed(BVF::try_from(*ubv).unwrap())
                }
                else {
                    BV::Dynamic(BVN::from(ubv))
                }
            }
        }

        impl From<$ubv> for BV {
            fn from(ubv: $ubv) -> Self {
                BV::from(&ubv)
            }
        }

        impl TryFrom<&'_ BV> for $ust {
            type Error = ConvertError;
            fn try_from(bv: &'_ BV) -> Result<Self, Self::Error> {
                match bv {
                    BV::Fixed(b) => Ok(<$ust>::try_from(b).unwrap()),
                    BV::Dynamic(b) => <$ust>::try_from(b),
                }
            }
        }

        impl TryFrom<BV> for $ust {
            type Error = ConvertError;
            fn try_from(bv: BV) -> Result<Self, Self::Error> {
                <$ust>::try_from(&bv)
            }
        }

        impl TryFrom<&'_ BV> for $ubv {
            type Error = ConvertError;
            fn try_from(bv: &'_ BV) -> Result<Self, Self::Error> {
                match bv {
                    BV::Fixed(b) => Ok(<$ubv>::from(*b)),
                    BV::Dynamic(b) => <$ubv>::try_from(b),
                }
            }
        }

        impl TryFrom<BV> for $ubv {
            type Error = ConvertError;
            fn try_from(bv: BV) -> Result<Self, Self::Error> {
                <$ubv>::try_from(&bv)
            }
        }
    )+
}}

#[cfg(target_pointer_width = "16")]
impl_froms!({(BV8, u8), (BV16, u16)}, {(BV32, u32), (BV64, u64), (BV128, u128)});
#[cfg(target_pointer_width = "32")]
impl_froms!({(BV8, u8), (BV16, u16), (BV32, u32)}, {(BV64, u64), (BV128, u128)});
#[cfg(target_pointer_width = "64")]
impl_froms!({(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64)}, {(BV128, u128)});

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

macro_rules! impl_op_assign { ($trait:ident, $method:ident, {$($sbv:ty),*}, {$($ubv:ty),*}) => {
    impl $trait<&'_ BV> for BV {
        fn $method(&mut self, bv: &'_ BV) {
            match bv {
                BV::Fixed(b) => self.$method(b),
                BV::Dynamic(b) => self.$method(b)
            }
        }
    }

    impl $trait<BV> for BV {
        fn $method(&mut self, rhs: BV) {
            self.$method(&rhs);
        }
    }

    $(
        impl $trait<&'_ $sbv> for BV {
            fn $method(&mut self, b: &'_ $sbv) {
                match self {
                    BV::Fixed(s) => s.$method(b),
                    BV::Dynamic(s) => s.$method(b)
                }
            }
        }

        impl $trait<$sbv> for BV {
            fn $method(&mut self, b: $sbv) {
                self.$method(&b);
            }
        }
    )+

    $(
        impl $trait<&'_ $ubv> for BV {
            fn $method(&mut self, b: &'_ $ubv) {
                if b.len() > self.len() {
                    self.reserve(b.len() - self.len());
                }
                match self {
                    BV::Fixed(s) => s.$method(BVF::try_from(b).unwrap()),
                    BV::Dynamic(s) => s.$method(b)
                }
            }
        }

        impl $trait<$ubv> for BV {
            fn $method(&mut self, b: $ubv) {
                self.$method(&b);
            }
        }
    )+
}}

macro_rules! impl_op { ($trait:ident, $method:ident, $assign_method:ident, {$($rhs:ty),+}) => {
    impl $trait<BV> for BV {
        type Output = BV;
        fn $method(mut self, rhs: BV) -> BV {
            self.$assign_method(rhs);
            return self;
        }
    }

    impl $trait<&'_ BV> for BV {
        type Output = BV;
        fn $method(mut self, rhs: &'_ BV) -> BV {
            self.$assign_method(rhs);
            return self;
        }
    }

    impl $trait<BV> for &'_ BV {
        type Output = BV;
        fn $method(self, rhs: BV) -> BV {
            return self.clone().$method(rhs);
        }
    }

    impl $trait<&'_ BV> for &'_ BV {
        type Output = BV;
        fn $method(self, rhs: &'_ BV) -> BV {
            return self.clone().$method(rhs);
        }
    }

    $(
        impl $trait<$rhs> for BV {
            type Output = BV;
            fn $method(mut self, rhs: $rhs) -> BV {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl $trait<&'_ $rhs> for BV {
            type Output = BV;
            fn $method(mut self, rhs: &'_ $rhs) -> BV {
                self.$assign_method(rhs);
                return self;
            }
        }

        impl $trait<$rhs> for &'_ BV {
            type Output = BV;
            fn $method(self, rhs: $rhs) -> BV {
                return self.clone().$method(rhs);
            }
        }

        impl $trait<&'_ $rhs> for &'_ BV {
            type Output = BV;
            fn $method(self, rhs: &'_ $rhs) -> BV {
                return self.clone().$method(rhs);
            }
        }
    )+
}}

macro_rules! impl_all_ops { ({$($sbv:ty),*}, {$($ubv:ty),*}) => {
    impl_op_assign!(BitAndAssign, bitand_assign, {$($sbv),*}, {$($ubv),*});
    impl_op_assign!(BitOrAssign, bitor_assign, {$($sbv),*}, {$($ubv),*});
    impl_op_assign!(BitXorAssign, bitxor_assign, {$($sbv),*}, {$($ubv),*});
    impl_op_assign!(AddAssign, add_assign, {$($sbv),*}, {$($ubv),*});
    impl_op_assign!(SubAssign, sub_assign, {$($sbv),*}, {$($ubv),*});
    impl_op!(BitAnd, bitand, bitand_assign, {$($sbv),* , $($ubv),*});
    impl_op!(BitOr, bitor, bitor_assign, {$($sbv),* , $($ubv),*});
    impl_op!(BitXor, bitxor, bitxor_assign, {$($sbv),* , $($ubv),*});
    impl_op!(Add, add, add_assign, {$($sbv),* , $($ubv),*});
    impl_op!(Sub, sub, sub_assign, {$($sbv),* , $($ubv),*});
}}

#[cfg(target_pointer_width = "16")]
impl_all_ops!({BV8, BV16, BV32}, {BV64, BV128, BVN});
#[cfg(target_pointer_width = "32")]
impl_all_ops!({BV8, BV16, BV32, BV64}, {BV128, BVN});
#[cfg(target_pointer_width = "64")]
impl_all_ops!({BV8, BV16, BV32, BV64, BV128}, {BVN});

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
