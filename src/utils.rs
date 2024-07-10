use std::fmt::{Debug, Display};
use std::mem::{align_of, size_of, size_of_val};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::Bit;

pub trait StaticCast<U> {
    fn cast_from(u: U) -> Self;
    fn cast_to(self) -> U;
}

macro_rules! impl_staticcast {
    ($($type:ty),+) => {
        impl_staticcast!(@1 {$($type),+}, {$($type),+});
    };
    (@1 {$($lhs:ty),+}, $rhs:tt) => {
        $(
            impl_staticcast!(@2 $lhs, $rhs);
        )+
    };
    (@2 $lhs:ty, {$($rhs:ty),+}) => {
        $(
            impl StaticCast<$rhs> for $lhs {
                fn cast_from(u: $rhs) -> Self {
                    u as Self
                }

                fn cast_to(self) -> $rhs {
                    self as $rhs
                }
            }
        )+
    };
}

impl_staticcast!(u8, u16, u32, u64, u128, usize);

pub trait Constants {
    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;
}

macro_rules! impl_constants {
    ($($type:ty),+) => {
        $(
            impl Constants for $type {
                const ZERO: Self = 0;
                const ONE: Self = 1;
                const MIN: Self = <$type>::MIN;
                const MAX: Self = <$type>::MAX;
            }
        )+
    }
}

impl_constants!(u8, u16, u32, u64, u128, usize);

pub trait Integer:
    Add<Output = Self>
    + AddAssign
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
    + Constants
    + Copy
    + Debug
    + Div<Output = Self>
    + DivAssign
    + Display
    + Eq
    + From<Bit>
    + Into<Bit>
    + Mul<Output = Self>
    + MulAssign
    + Not<Output = Self>
    + Ord
    + PartialEq
    + PartialOrd
    + Shl<usize, Output = Self>
    + ShlAssign<usize>
    + Shr<usize, Output = Self>
    + ShrAssign<usize>
    + Sub<Output = Self>
    + SubAssign
    + Sized
    + StaticCast<u8>
    + StaticCast<u16>
    + StaticCast<u32>
    + StaticCast<u64>
    + StaticCast<u128>
    + StaticCast<Self>
{
    fn cadd(&mut self, rhs: Self, carry: Self) -> Self;
    fn csub(&mut self, rhs: Self, carry: Self) -> Self;
    fn wmul(&self, rhs: Self) -> (Self, Self);
    fn leading_zeros(&self) -> usize;
    fn leading_ones(&self) -> usize;
    fn trailing_zeros(&self) -> usize;
    fn trailing_ones(&self) -> usize;
}

impl Integer for u8 {
    fn cadd(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn csub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn wmul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u16) * (rhs as u16);
        (res as Self, (res >> Self::BITS) as Self)
    }

    fn leading_zeros(&self) -> usize {
        u8::leading_zeros(*self) as usize
    }

    fn leading_ones(&self) -> usize {
        u8::leading_ones(*self) as usize
    }

    fn trailing_zeros(&self) -> usize {
        u8::trailing_zeros(*self) as usize
    }

    fn trailing_ones(&self) -> usize {
        u8::trailing_ones(*self) as usize
    }
}

impl Integer for u16 {
    fn cadd(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn csub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn wmul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u32) * (rhs as u32);
        (res as Self, (res >> Self::BITS) as Self)
    }

    fn leading_zeros(&self) -> usize {
        u16::leading_zeros(*self) as usize
    }

    fn leading_ones(&self) -> usize {
        u16::leading_ones(*self) as usize
    }

    fn trailing_zeros(&self) -> usize {
        u16::trailing_zeros(*self) as usize
    }

    fn trailing_ones(&self) -> usize {
        u16::trailing_ones(*self) as usize
    }
}

impl Integer for u32 {
    fn cadd(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn csub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn wmul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u64) * (rhs as u64);
        (res as Self, (res >> Self::BITS) as Self)
    }

    fn leading_zeros(&self) -> usize {
        u32::leading_zeros(*self) as usize
    }

    fn leading_ones(&self) -> usize {
        u32::leading_ones(*self) as usize
    }

    fn trailing_zeros(&self) -> usize {
        u32::trailing_zeros(*self) as usize
    }

    fn trailing_ones(&self) -> usize {
        u32::trailing_ones(*self) as usize
    }
}

impl Integer for u64 {
    fn cadd(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn csub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn wmul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u128) * (rhs as u128);
        (res as Self, (res >> Self::BITS) as Self)
    }

    fn leading_zeros(&self) -> usize {
        u64::leading_zeros(*self) as usize
    }

    fn leading_ones(&self) -> usize {
        u64::leading_ones(*self) as usize
    }

    fn trailing_zeros(&self) -> usize {
        u64::trailing_zeros(*self) as usize
    }

    fn trailing_ones(&self) -> usize {
        u64::trailing_ones(*self) as usize
    }
}

impl Integer for usize {
    fn cadd(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn csub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn wmul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u128) * (rhs as u128);
        (res as Self, (res >> Self::BITS) as Self)
    }

    fn leading_zeros(&self) -> usize {
        usize::leading_zeros(*self) as usize
    }

    fn leading_ones(&self) -> usize {
        usize::leading_ones(*self) as usize
    }

    fn trailing_zeros(&self) -> usize {
        usize::trailing_zeros(*self) as usize
    }

    fn trailing_ones(&self) -> usize {
        usize::trailing_ones(*self) as usize
    }
}

impl Integer for u128 {
    fn cadd(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn csub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        c1 as Self + c2 as Self
    }

    fn wmul(&self, rhs: Self) -> (Self, Self) {
        let mask = (1u128 << (Self::BITS / 2)) - 1;
        let mut p0 = (self & mask).wrapping_mul(rhs & mask);
        let p1 = (*self >> (Self::BITS / 2)).wrapping_mul(rhs & mask);
        let p2 = (self & mask).wrapping_mul(rhs >> (Self::BITS / 2));
        let p3 = (*self >> (Self::BITS / 2)).wrapping_mul(rhs >> (Self::BITS / 2));
        let c = p0.cadd(p1 << 64, p2 << 64);
        (p0, p3 + (p1 >> 64) + (p2 >> 64) + c)
    }

    fn leading_zeros(&self) -> usize {
        u128::leading_zeros(*self) as usize
    }

    fn leading_ones(&self) -> usize {
        u128::leading_ones(*self) as usize
    }

    fn trailing_zeros(&self) -> usize {
        u128::trailing_zeros(*self) as usize
    }

    fn trailing_ones(&self) -> usize {
        u128::trailing_ones(*self) as usize
    }
}

pub trait IArray {
    type I: Integer;
    fn int_len<J: Integer>(&self) -> usize
    where
        Self::I: StaticCast<J>;

    fn get_int<J: Integer>(&self, idx: usize) -> Option<J>
    where
        Self::I: StaticCast<J>;
}

pub trait IArrayMut {
    type I: Integer;
    fn set_int<J: Integer>(&mut self, idx: usize, v: J) -> Option<J>
    where
        Self::I: StaticCast<J>;
}

#[cfg(not(any(target_endian = "big", target_endian = "little")))]
compile_error!("Unknown target endianness");

#[cfg(target_endian = "little")]
impl<I: Integer> IArray for [I] {
    type I = I;

    fn int_len<J: Integer>(&self) -> usize
    where
        I: StaticCast<J>,
    {
        (size_of_val(self) + size_of::<J>() - 1) / size_of::<J>()
    }

    fn get_int<J: Integer>(&self, idx: usize) -> Option<J>
    where
        I: StaticCast<J>,
    {
        // The conditional check should be optimized during specialization.
        // These asserts should be validated by our tests.
        if size_of::<I>() >= size_of::<J>() {
            unsafe {
                debug_assert!(size_of::<I>() % size_of::<J>() == 0);
                debug_assert!(align_of::<I>() % align_of::<J>() == 0);
                let (head, mid, tail) = self.align_to::<J>();
                debug_assert!(head.is_empty() && tail.is_empty());
                if idx < mid.len() {
                    Some(mid[idx])
                } else {
                    None
                }
            }
        } else {
            debug_assert!(size_of::<J>() % size_of::<I>() == 0);
            let s = size_of::<J>() / size_of::<I>();
            let mut v = J::ZERO;
            if idx >= IArray::int_len::<J>(self) {
                return None;
            }
            for i in 0..s {
                v |= StaticCast::<J>::cast_to(*self.get(idx * s + i).unwrap_or(&I::ZERO))
                    << (size_of::<I>() * 8 * i);
            }
            Some(v)
        }
    }
}

#[cfg(target_endian = "little")]
impl<I: Integer> IArrayMut for [I] {
    type I = I;

    fn set_int<J: Integer>(&mut self, idx: usize, v: J) -> Option<J>
    where
        I: StaticCast<J>,
    {
        // The conditional check should be optimized during specialization.
        // These asserts should be validated by our tests.
        if size_of::<I>() >= size_of::<J>() {
            unsafe {
                debug_assert!(size_of::<I>() % size_of::<J>() == 0);
                debug_assert!(align_of::<I>() % align_of::<J>() == 0);
                let (head, mid, tail) = self.align_to_mut::<J>();
                debug_assert!(head.is_empty() && tail.is_empty());
                if idx < mid.len() {
                    let old = mid[idx];
                    mid[idx] = v;
                    Some(old)
                } else {
                    None
                }
            }
        } else {
            debug_assert!(size_of::<J>() % size_of::<I>() == 0);
            let s = size_of::<J>() / size_of::<I>();
            let mut old = J::ZERO;
            if idx >= IArray::int_len::<J>(self) {
                return None;
            }
            for i in 0..s {
                if let Some(p) = self.get_mut(idx * s + i) {
                    old |= StaticCast::<J>::cast_to(*p) << (size_of::<I>() * 8 * i);
                    *p = StaticCast::<J>::cast_from(v >> (size_of::<I>() * 8 * i));
                }
            }
            Some(old)
        }
    }
}

// TODO: Big Endian support for IArray and IArrayMut
#[cfg(target_endian = "big")]
compile_error!("Big endian not yet supported");
