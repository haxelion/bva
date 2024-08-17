use std::cmp::Ordering;
use std::fmt::{Binary, Display, LowerHex, Octal, UpperHex};

use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Range, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::dynamic::Bvd;
#[allow(unused_imports)]
use crate::fixed::{Bv128, Bv16, Bv32, Bv64, Bv8, Bvf};
use crate::iter::BitIterator;
use crate::utils::{IArray, IArrayMut, Integer, StaticCast};
use crate::Bit;
use crate::{BitVector, ConvertionError, Endianness};

// Choose a fixed Bvf type which should match the size of Bvd inside the enum
#[cfg(target_pointer_width = "16")]
pub(crate) type Bvp = Bv32;
#[cfg(target_pointer_width = "32")]
pub(crate) type Bvp = Bv64;
#[cfg(target_pointer_width = "64")]
pub(crate) type Bvp = Bv128;

// ------------------------------------------------------------------------------------------------
// Bit Vector automatic allocation implementation
// ------------------------------------------------------------------------------------------------

/// A bit vector with an automatically managed memory allocation type.
///
/// Depending on the required capacity, it might use a fixed capacity implementation to avoid
/// unnecessary dynamic memory allocations, or it might use a dynamic capacity implementation
/// when needed.
///
/// While avoiding memory allocation might improve performances, there is a slight performance cost
/// due to the dynamic dispatch and extra capacity checks. The net effect will depend on the exact
/// workload.
///
/// # Examples
///
/// ```
/// use bva::{BitVector, Bv};
///
/// // This bit vector will be stack allocated.
/// let a = Bv::from(27u8);
/// assert_eq!(a.len(), 8);
/// // This bit vector will be heap allocated.
/// let b = Bv::ones(256);
/// assert_eq!(b.len(), 256);
/// // The result of this operation will also be heap allocated.
/// let c = b + a;
/// assert_eq!(c.len(), 256);
/// assert_eq!(c.to_string(), "26");
/// ```
#[derive(Clone, Debug)]
pub enum Bv {
    #[doc(hidden)]
    Fixed(Bvp),
    #[doc(hidden)]
    Dynamic(Bvd),
}

impl Bv {
    /// Reserve will reserve room for at least `additional` bits in the bit vector. The actual
    /// length of the bit vector will stay unchanged, see [`BitVector::resize`] to change the actual
    /// length of the bit vector.
    ///
    /// Calling this method might cause the storage to become dynamically allocated.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let mut bv = Bv::ones(128);
    /// assert_eq!(bv.capacity(), 128);
    /// bv.reserve(128);
    /// assert_eq!(bv.capacity(), 256);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        match self {
            &mut Bv::Fixed(ref b) => {
                if b.len() + additional > Bvp::capacity() {
                    let mut new_b = Bvd::from(b);
                    new_b.reserve(additional);
                    *self = Bv::Dynamic(new_b);
                }
            }
            Bv::Dynamic(b) => b.reserve(additional),
        }
    }

    /// Drop as much excess capacity as possible in the bit vector to fit the current length.
    ///
    /// Calling this method might cause the implementation to drop unnecessary dynamically
    /// allocated memory.
    ///
    /// ```
    /// use bva::{BitVector, Bv};
    ///
    /// let mut bv = Bv::ones(128);
    /// bv.reserve(128);
    /// assert_eq!(bv.capacity(), 256);
    /// bv.shrink_to_fit();
    /// assert_eq!(bv.capacity(), 128);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        if let Bv::Dynamic(b) = self {
            if b.len() <= Bvp::capacity() {
                let new_b = Bvp::try_from(&*b).unwrap();
                *self = Bv::Fixed(new_b);
            } else {
                b.shrink_to_fit();
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------
// Bv - Integer Array traits
// ------------------------------------------------------------------------------------------------

impl IArray for Bv {
    type I = u64;

    fn int_len<J: Integer>(&self) -> usize
    where
        u64: StaticCast<J>,
    {
        match self {
            Bv::Fixed(bvf) => IArray::int_len(bvf),
            Bv::Dynamic(bvd) => IArray::int_len(bvd),
        }
    }

    fn get_int<J: Integer>(&self, idx: usize) -> Option<J>
    where
        u64: StaticCast<J>,
    {
        match self {
            Bv::Fixed(bvf) => IArray::get_int(bvf, idx),
            Bv::Dynamic(bvd) => IArray::get_int(bvd, idx),
        }
    }
}

impl IArrayMut for Bv {
    type I = u64;

    fn set_int<J: Integer>(&mut self, idx: usize, v: J) -> Option<J>
    where
        u64: StaticCast<J>,
    {
        match self {
            Bv::Fixed(bvf) => IArrayMut::set_int(bvf, idx, v),
            Bv::Dynamic(bvd) => IArrayMut::set_int(bvd, idx, v),
        }
    }
}

// ------------------------------------------------------------------------------------------------
// Bv - Bit Vector core trait
// ------------------------------------------------------------------------------------------------

impl BitVector for Bv {
    fn with_capacity(capacity: usize) -> Self {
        if capacity <= Bvp::capacity() {
            Bv::Fixed(Bvp::with_capacity(capacity))
        } else {
            Bv::Dynamic(Bvd::with_capacity(capacity))
        }
    }

    fn zeros(length: usize) -> Self {
        if length <= Bvp::capacity() {
            Bv::Fixed(Bvp::zeros(length))
        } else {
            Bv::Dynamic(Bvd::zeros(length))
        }
    }

    fn ones(length: usize) -> Self {
        if length <= Bvp::capacity() {
            Bv::Fixed(Bvp::ones(length))
        } else {
            Bv::Dynamic(Bvd::ones(length))
        }
    }

    fn capacity(&self) -> usize {
        match self {
            Bv::Fixed(_) => Bvp::capacity(),
            Bv::Dynamic(b) => b.capacity(),
        }
    }

    fn len(&self) -> usize {
        match self {
            Bv::Fixed(b) => b.len(),
            Bv::Dynamic(b) => b.len(),
        }
    }

    fn from_binary<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError> {
        if string.as_ref().len() <= Bvp::capacity() {
            Ok(Bv::Fixed(Bvp::from_binary(string)?))
        } else {
            Ok(Bv::Dynamic(Bvd::from_binary(string)?))
        }
    }

    fn from_hex<S: AsRef<str>>(string: S) -> Result<Self, ConvertionError> {
        if string.as_ref().len() * 4 <= Bvp::capacity() {
            Ok(Bv::Fixed(Bvp::from_hex(string)?))
        } else {
            Ok(Bv::Dynamic(Bvd::from_hex(string)?))
        }
    }

    fn from_bytes<B: AsRef<[u8]>>(
        bytes: B,
        endianness: Endianness,
    ) -> Result<Self, ConvertionError> {
        if bytes.as_ref().len() * 8 <= Bvp::capacity() {
            Ok(Bv::Fixed(Bvp::from_bytes(bytes, endianness)?))
        } else {
            Ok(Bv::Dynamic(Bvd::from_bytes(bytes, endianness)?))
        }
    }

    fn to_vec(&self, endianness: Endianness) -> Vec<u8> {
        match self {
            Bv::Fixed(b) => b.to_vec(endianness),
            Bv::Dynamic(b) => b.to_vec(endianness),
        }
    }

    fn read<R: std::io::Read>(
        reader: &mut R,
        length: usize,
        endianness: Endianness,
    ) -> std::io::Result<Self> {
        if length <= Bvp::capacity() {
            Ok(Bv::Fixed(Bvp::read(reader, length, endianness)?))
        } else {
            Ok(Bv::Dynamic(Bvd::read(reader, length, endianness)?))
        }
    }

    fn write<W: std::io::Write>(
        &self,
        writer: &mut W,
        endianness: Endianness,
    ) -> std::io::Result<()> {
        match self {
            Bv::Fixed(b) => b.write(writer, endianness),
            Bv::Dynamic(b) => b.write(writer, endianness),
        }
    }

    fn get(&self, index: usize) -> Bit {
        match self {
            Bv::Fixed(b) => b.get(index),
            Bv::Dynamic(b) => b.get(index),
        }
    }

    fn set(&mut self, index: usize, bit: Bit) {
        match self {
            Bv::Fixed(b) => b.set(index, bit),
            Bv::Dynamic(b) => b.set(index, bit),
        }
    }

    fn copy_range(&self, range: Range<usize>) -> Self {
        match self {
            Bv::Fixed(b) => Bv::Fixed(b.copy_range(range)),
            Bv::Dynamic(b) => {
                let s = b.copy_range(range);
                if s.len() <= Bvp::capacity() {
                    Bv::Fixed(Bvp::try_from(s).unwrap())
                } else {
                    Bv::Dynamic(s)
                }
            }
        }
    }

    fn push(&mut self, bit: Bit) {
        self.reserve(1);
        match self {
            Bv::Fixed(b) => b.push(bit),
            Bv::Dynamic(b) => b.push(bit),
        }
    }

    fn pop(&mut self) -> Option<Bit> {
        match self {
            Bv::Fixed(b) => b.pop(),
            Bv::Dynamic(b) => b.pop(),
        }
    }

    fn resize(&mut self, new_length: usize, bit: Bit) {
        if new_length > self.len() {
            self.reserve(new_length - self.len());
        }
        match self {
            Bv::Fixed(b) => b.resize(new_length, bit),
            Bv::Dynamic(b) => b.resize(new_length, bit),
        }
    }

    fn append<B: BitVector>(&mut self, suffix: &B) {
        match self {
            Bv::Fixed(bvf) => {
                if bvf.len() + suffix.len() <= Bvp::capacity() {
                    bvf.append(suffix);
                } else {
                    let mut bvd = Bvd::from(&*bvf);
                    bvd.append(suffix);
                    *self = Bv::Dynamic(bvd);
                }
            }
            Bv::Dynamic(bvd) => {
                bvd.append(suffix);
            }
        }
    }

    fn prepend<B: BitVector>(&mut self, prefix: &B) {
        match self {
            Bv::Fixed(bvf) => {
                if bvf.len() + prefix.len() <= Bvp::capacity() {
                    bvf.prepend(prefix);
                } else {
                    let mut bvd = Bvd::from(&*bvf);
                    bvd.prepend(prefix);
                    *self = Bv::Dynamic(bvd);
                }
            }
            Bv::Dynamic(bvd) => {
                bvd.prepend(prefix);
            }
        }
    }

    fn shl_in(&mut self, bit: Bit) -> Bit {
        match self {
            Bv::Fixed(b) => b.shl_in(bit),
            Bv::Dynamic(b) => b.shl_in(bit),
        }
    }

    fn shr_in(&mut self, bit: Bit) -> Bit {
        match self {
            Bv::Fixed(b) => b.shr_in(bit),
            Bv::Dynamic(b) => b.shr_in(bit),
        }
    }

    fn rotl(&mut self, rot: usize) {
        match self {
            Bv::Fixed(b) => b.rotl(rot),
            Bv::Dynamic(b) => b.rotl(rot),
        }
    }

    fn rotr(&mut self, rot: usize) {
        match self {
            Bv::Fixed(b) => b.rotr(rot),
            Bv::Dynamic(b) => b.rotr(rot),
        }
    }

    fn leading_zeros(&self) -> usize {
        match self {
            Bv::Fixed(b) => b.leading_zeros(),
            Bv::Dynamic(b) => b.leading_zeros(),
        }
    }

    fn leading_ones(&self) -> usize {
        match self {
            Bv::Fixed(b) => b.leading_ones(),
            Bv::Dynamic(b) => b.leading_ones(),
        }
    }

    fn trailing_zeros(&self) -> usize {
        match self {
            Bv::Fixed(b) => b.trailing_zeros(),
            Bv::Dynamic(b) => b.trailing_zeros(),
        }
    }

    fn trailing_ones(&self) -> usize {
        match self {
            Bv::Fixed(b) => b.trailing_ones(),
            Bv::Dynamic(b) => b.trailing_ones(),
        }
    }

    fn is_zero(&self) -> bool {
        match self {
            Bv::Fixed(b) => b.is_zero(),
            Bv::Dynamic(b) => b.is_zero(),
        }
    }

    fn div_rem<B: BitVector>(&self, divisor: &B) -> (Self, Self)
    where
        Self: for<'a> TryFrom<&'a B, Error: std::fmt::Debug>,
    {
        assert!(!divisor.is_zero(), "Division by zero");
        let mut quotient = Bv::zeros(self.len());
        let mut rem = self.clone();
        if divisor.significant_bits() > self.significant_bits() {
            return (quotient, rem);
        }

        let shift = self.significant_bits() - divisor.significant_bits();
        let mut divisor: Bv = divisor.try_into().expect("should never fail");
        divisor.resize(self.len(), Bit::Zero);
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
// Bv - Bit iterator trait
// ------------------------------------------------------------------------------------------------

impl<'a> IntoIterator for &'a Bv {
    type Item = Bit;
    type IntoIter = BitIterator<'a, Bv>;

    fn into_iter(self) -> Self::IntoIter {
        BitIterator::new(self)
    }
}

impl FromIterator<Bit> for Bv {
    fn from_iter<T: IntoIterator<Item = Bit>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut bv = Bv::with_capacity(iter.size_hint().0);
        iter.for_each(|b| bv.push(b));
        bv
    }
}

impl Extend<Bit> for Bv {
    fn extend<T: IntoIterator<Item = Bit>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        iter.for_each(|b| self.push(b));
    }
}

// ------------------------------------------------------------------------------------------------
// Bv - Formatting traits
// ------------------------------------------------------------------------------------------------

impl Binary for Bv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bv::Fixed(b) => Binary::fmt(b, f),
            Bv::Dynamic(b) => Binary::fmt(b, f),
        }
    }
}

impl Display for Bv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bv::Fixed(b) => Display::fmt(b, f),
            Bv::Dynamic(b) => Display::fmt(b, f),
        }
    }
}

impl LowerHex for Bv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bv::Fixed(b) => LowerHex::fmt(b, f),
            Bv::Dynamic(b) => LowerHex::fmt(b, f),
        }
    }
}

impl UpperHex for Bv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bv::Fixed(b) => UpperHex::fmt(b, f),
            Bv::Dynamic(b) => UpperHex::fmt(b, f),
        }
    }
}

impl Octal for Bv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bv::Fixed(b) => Octal::fmt(b, f),
            Bv::Dynamic(b) => Octal::fmt(b, f),
        }
    }
}

// ------------------------------------------------------------------------------------------------
// Bv - Comparison traits
// ------------------------------------------------------------------------------------------------

impl PartialEq for Bv {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Bv::Fixed(b1) => match other {
                Bv::Fixed(b2) => b1.eq(b2),
                Bv::Dynamic(b2) => b1.eq(b2),
            },
            Bv::Dynamic(b1) => match other {
                Bv::Fixed(b2) => b1.eq(b2),
                Bv::Dynamic(b2) => b1.eq(b2),
            },
        }
    }
}

impl PartialEq<Bvd> for Bv {
    fn eq(&self, other: &Bvd) -> bool {
        match self {
            Bv::Fixed(bvf) => bvf.eq(other),
            Bv::Dynamic(bvd) => bvd.eq(other),
        }
    }
}

impl<I: Integer, const N: usize> PartialEq<Bvf<I, N>> for Bv
where
    u64: StaticCast<I>,
{
    fn eq(&self, other: &Bvf<I, N>) -> bool {
        match self {
            Bv::Fixed(bvf) => bvf.eq(other),
            Bv::Dynamic(bvd) => bvd.eq(other),
        }
    }
}

impl Eq for Bv {}

impl PartialOrd for Bv {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: Integer, const N: usize> PartialOrd<Bvf<I, N>> for Bv
where
    u64: StaticCast<I>,
{
    fn partial_cmp(&self, other: &Bvf<I, N>) -> Option<Ordering> {
        match self {
            Bv::Fixed(bvf) => bvf.partial_cmp(other),
            Bv::Dynamic(bvd) => bvd.partial_cmp(other),
        }
    }
}

impl PartialOrd<Bvd> for Bv {
    fn partial_cmp(&self, other: &Bvd) -> Option<Ordering> {
        match self {
            Bv::Fixed(bvf) => bvf.partial_cmp(other),
            Bv::Dynamic(bvd) => bvd.partial_cmp(other),
        }
    }
}

impl Ord for Bv {
    fn cmp(&self, other: &Self) -> Ordering {
        match self {
            Bv::Fixed(b1) => match other {
                Bv::Fixed(b2) => b1.cmp(b2),
                Bv::Dynamic(b2) => b1.partial_cmp(b2).unwrap(),
            },
            Bv::Dynamic(b1) => match other {
                Bv::Fixed(b2) => b1.partial_cmp(b2).unwrap(),
                Bv::Dynamic(b2) => b1.cmp(b2),
            },
        }
    }
}

// ------------------------------------------------------------------------------------------------
// Bv - Conversion traits
// ------------------------------------------------------------------------------------------------

impl From<&Bv> for Bv {
    fn from(b: &Bv) -> Self {
        match b {
            Bv::Fixed(bvf) => Bv::Fixed(*bvf),
            Bv::Dynamic(bvd) => Bv::Dynamic(bvd.clone()),
        }
    }
}

impl From<Bvd> for Bv {
    fn from(b: Bvd) -> Self {
        if let Ok(bvf) = Bvp::try_from(&b) {
            Bv::Fixed(bvf)
        } else {
            Bv::Dynamic(b)
        }
    }
}

impl From<&'_ Bvd> for Bv {
    fn from(b: &'_ Bvd) -> Self {
        if let Ok(bvf) = Bvp::try_from(b) {
            Bv::Fixed(bvf)
        } else {
            Bv::Dynamic(b.clone())
        }
    }
}

impl<I: Integer, const N: usize> From<&Bvf<I, N>> for Bv {
    fn from(b: &Bvf<I, N>) -> Self {
        if Bvf::<I, N>::capacity() <= Bvp::capacity() {
            Bv::Fixed(b.try_into().unwrap())
        } else {
            Bv::Dynamic(b.into())
        }
    }
}

impl<I: Integer, const N: usize> From<Bvf<I, N>> for Bv {
    fn from(b: Bvf<I, N>) -> Self {
        Bv::from(&b)
    }
}

macro_rules! impl_tryfrom { ($($type:ty),+) => {
    $(
        impl From<$type> for Bv {
            fn from(int: $type) -> Self {
                // Branch should be optimized at compile time
                if std::mem::size_of::<$type>() * 8 <= Bvp::capacity() {
                    Bv::Fixed(Bvp::try_from(int).unwrap())
                }
                else {
                    Bv::Dynamic(Bvd::from(int))
                }
            }
        }

        impl From<&$type> for Bv {
            fn from(int: &$type) -> Self {
                Self::from(*int)
            }
        }

        impl TryFrom<&Bv> for $type
        {
            type Error = ConvertionError;
            fn try_from(bv: &Bv) -> Result<Self, Self::Error> {
                match bv {
                    Bv::Fixed(b) => Ok(b.try_into()?),
                    Bv::Dynamic(b) => Ok(b.try_into()?),
                }
            }
        }

        impl TryFrom<Bv> for $type
        {
            type Error = ConvertionError;
            fn try_from(bv: Bv) -> Result<Self, Self::Error> {
                Self::try_from(&bv)
            }
        }
    )+
}}

impl_tryfrom!(u8, u16, u32, u64, u128, usize);

impl<I: Integer> From<&[I]> for Bv
where
    u64: StaticCast<I>,
{
    fn from(slice: &[I]) -> Self {
        let mut bv = Bv::zeros(slice.len() * I::BITS);
        for (i, v) in slice.iter().enumerate() {
            bv.set_int(i, *v);
        }
        bv
    }
}

// ------------------------------------------------------------------------------------------------
// Bv - Unary operator & shifts
// ------------------------------------------------------------------------------------------------

impl Not for Bv {
    type Output = Bv;

    fn not(self) -> Self::Output {
        match self {
            Bv::Fixed(b) => Bv::Fixed(b.not()),
            Bv::Dynamic(b) => Bv::Dynamic(b.not()),
        }
    }
}

impl Not for &'_ Bv {
    type Output = Bv;

    fn not(self) -> Self::Output {
        match self {
            Bv::Fixed(b) => Bv::Fixed(b.not()),
            Bv::Dynamic(b) => Bv::Dynamic(b.not()),
        }
    }
}

macro_rules! impl_shift_assign {($trait:ident, $method:ident, {$($rhs:ty),+}) => {
    $(
        impl $trait<$rhs> for Bv {
            fn $method(&mut self, rhs: $rhs) {
                match self {
                    Bv::Fixed(b) => b.$method(rhs),
                    Bv::Dynamic(b) => b.$method(rhs)
                }
            }
        }

        impl $trait<&'_ $rhs> for Bv {
            fn $method(&mut self, rhs: &'_ $rhs) {
                match self {
                    Bv::Fixed(b) => b.$method(rhs),
                    Bv::Dynamic(b) => b.$method(rhs)
                }
            }
        }
    )+
}}

impl_shift_assign!(ShlAssign, shl_assign, {u8, u16, u32, u64, u128, usize});
impl_shift_assign!(ShrAssign, shr_assign, {u8, u16, u32, u64, u128, usize});

macro_rules! impl_shift {($trait:ident, $method:ident, {$($rhs:ty),+}) => {
    $(
        impl $trait<$rhs> for Bv {
            type Output = Bv;
            fn $method(self, rhs: $rhs) -> Bv {
                match self {
                    Bv::Fixed(b) => Bv::Fixed(b.$method(rhs)),
                    Bv::Dynamic(b) => Bv::Dynamic(b.$method(rhs))
                }
            }
        }

        impl $trait<&'_ $rhs> for Bv {
            type Output = Bv;
            fn $method(self, rhs: &'_ $rhs) -> Bv {
                match self {
                    Bv::Fixed(b) => Bv::Fixed(b.$method(rhs)),
                    Bv::Dynamic(b) => Bv::Dynamic(b.$method(rhs))
                }
            }
        }

        impl $trait<$rhs> for &'_ Bv {
            type Output = Bv;
            fn $method(self, rhs: $rhs) -> Bv {
                self.clone().$method(rhs)
            }
        }

        impl $trait<&'_ $rhs> for &'_ Bv {
            type Output = Bv;
            fn $method(self, rhs: &'_ $rhs) -> Bv {
                self.clone().$method(rhs)
            }
        }
    )+
}}

impl_shift!(Shl, shl, {u8, u16, u32, u64, u128, usize});
impl_shift!(Shr, shr, {u8, u16, u32, u64, u128, usize});

// ------------------------------------------------------------------------------------------------
// Uint helper macro
// ------------------------------------------------------------------------------------------------

macro_rules! impl_op_uint {
    ($trait:ident, $method:ident, {$($uint:ty),+}) => {
        $(
            impl $trait<&$uint> for &Bv
            {
                type Output = Bv;
                fn $method(self, rhs: &$uint) -> Self::Output {
                    match self {
                        Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                        Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                    }
                }
            }

            impl $trait<$uint> for &Bv
            {
                type Output = Bv;
                fn $method(self, rhs: $uint) -> Self::Output {
                    match self {
                        Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                        Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                    }
                }
            }

            impl $trait<&$uint> for Bv
            {
                type Output = Bv;
                fn $method(self, rhs: &$uint) -> Self::Output {
                    match self {
                        Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                        Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                    }
                }
            }

            impl $trait<$uint> for Bv
            {
                type Output = Bv;
                fn $method(self, rhs: $uint) -> Self::Output {
                    match self {
                        Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                        Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                    }
                }
            }
        )+
    };
}

macro_rules! impl_op_assign_uint {
    ($trait:ident, $method:ident, {$($uint:ty),+}) => {
        $(
            impl $trait<$uint> for Bv
            {
                fn $method(&mut self, rhs: $uint) {
                    match self {
                        Bv::Fixed(bvf) => bvf.$method(rhs),
                        Bv::Dynamic(bvd) => bvd.$method(rhs),
                    }
                }
            }

            impl $trait<&$uint> for Bv
            {
                fn $method(&mut self, rhs: &$uint) {
                    match self {
                        Bv::Fixed(bvf) => bvf.$method(rhs),
                        Bv::Dynamic(bvd) => bvd.$method(rhs),
                    }
                }
            }
        )+
    };
}

// ------------------------------------------------------------------------------------------------
// Bv - Arithmetic operators (assignment kind)
// ------------------------------------------------------------------------------------------------

macro_rules! impl_op_assign {
    ($trait:ident, $method:ident, {$($uint:ty),+}) => {
        impl $trait<&Bv> for Bv {
            fn $method(&mut self, bv: &Bv) {
                match bv {
                    Bv::Fixed(b) => self.$method(b),
                    Bv::Dynamic(b) => self.$method(b),
                }
            }
        }

        impl $trait<Bv> for Bv {
            fn $method(&mut self, bv: Bv) {
                match bv {
                    Bv::Fixed(b) => self.$method(b),
                    Bv::Dynamic(b) => self.$method(b),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<&Bvf<I, N>> for Bv
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, bvf: &Bvf<I, N>) {
                match self {
                    Bv::Fixed(b) => b.$method(bvf),
                    Bv::Dynamic(b) => b.$method(bvf),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<Bvf<I, N>> for Bv
        where
            u64: StaticCast<I>,
        {
            fn $method(&mut self, bvf: Bvf<I, N>) {
                match self {
                    Bv::Fixed(b) => b.$method(bvf),
                    Bv::Dynamic(b) => b.$method(bvf),
                }
            }
        }

        impl $trait<Bvd> for Bv {
            fn $method(&mut self, bvd: Bvd) {
                match self {
                    Bv::Fixed(b) => b.$method(bvd),
                    Bv::Dynamic(b) => b.$method(bvd),
                }
            }
        }

        impl $trait<&Bvd> for Bv {
            fn $method(&mut self, bvd: &Bvd) {
                match self {
                    Bv::Fixed(b) => b.$method(bvd),
                    Bv::Dynamic(b) => b.$method(bvd),
                }
            }
        }

        impl_op_assign_uint!($trait, $method, {$($uint),+});
    };
}

impl_op_assign!(BitAndAssign, bitand_assign, {u8, u16, u32, u64, usize, u128});
impl_op_assign!(BitOrAssign, bitor_assign, {u8, u16, u32, u64, usize, u128});
impl_op_assign!(BitXorAssign, bitxor_assign, {u8, u16, u32, u64, usize, u128});
impl_op_assign!(AddAssign, add_assign, {u8, u16, u32, u64, usize, u128});
impl_op_assign!(SubAssign, sub_assign, {u8, u16, u32, u64, usize, u128});
impl_op_assign!(MulAssign, mul_assign, {u8, u16, u32, u64, usize, u128});
impl_op_assign!(DivAssign, div_assign, {u8, u16, u32, u64, usize, u128});
impl_op_assign!(RemAssign, rem_assign, {u8, u16, u32, u64, usize, u128});

macro_rules! impl_op {
    ($trait:ident, $method:ident, {$($uint:ty),+}) => {
        impl $trait<&Bv> for &Bv {
            type Output = Bv;
            fn $method(self, rhs: &Bv) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl $trait<Bv> for &Bv {
            type Output = Bv;
            fn $method(self, rhs: Bv) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl $trait<&Bv> for Bv {
            type Output = Bv;
            fn $method(self, rhs: &Bv) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl $trait<Bv> for Bv {
            type Output = Bv;
            fn $method(self, rhs: Bv) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<&Bvf<I, N>> for &Bv
        where
            u64: StaticCast<I>
        {
            type Output = Bv;
            fn $method(self, rhs: &Bvf<I, N>) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<Bvf<I, N>> for &Bv
        where
            u64: StaticCast<I>
        {
            type Output = Bv;
            fn $method(self, rhs: Bvf<I, N>) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<&Bvf<I, N>> for Bv
        where
            u64: StaticCast<I>
        {
            type Output = Bv;
            fn $method(self, rhs: &Bvf<I, N>) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl<I: Integer, const N: usize> $trait<Bvf<I, N>> for Bv
        where
            u64: StaticCast<I>
        {
            type Output = Bv;
            fn $method(self, rhs: Bvf<I, N>) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl $trait<&Bvd> for &Bv
        {
            type Output = Bv;
            fn $method(self, rhs: &Bvd) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl $trait<Bvd> for &Bv
        {
            type Output = Bv;
            fn $method(self, rhs: Bvd) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl $trait<&Bvd> for Bv
        {
            type Output = Bv;
            fn $method(self, rhs: &Bvd) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl $trait<Bvd> for Bv
        {
            type Output = Bv;
            fn $method(self, rhs: Bvd) -> Bv {
                match self {
                    Bv::Fixed(bvf) => Bv::Fixed(bvf.$method(rhs)),
                    Bv::Dynamic(bvd) => Bv::Dynamic(bvd.$method(rhs)),
                }
            }
        }

        impl_op_uint!($trait, $method, {$($uint),+});
    };
}

impl_op!(BitAnd, bitand, {u8, u16, u32, u64, usize, u128});
impl_op!(BitOr, bitor, {u8, u16, u32, u64, usize, u128});
impl_op!(BitXor, bitxor, {u8, u16, u32, u64, usize, u128});
impl_op!(Add, add, {u8, u16, u32, u64, usize, u128});
impl_op!(Sub, sub, {u8, u16, u32, u64, usize, u128});
impl_op!(Mul, mul, {u8, u16, u32, u64, usize, u128});
impl_op!(Div, div, {u8, u16, u32, u64, usize, u128});
impl_op!(Rem, rem, {u8, u16, u32, u64, usize, u128});
