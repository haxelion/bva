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
    + StaticCast<u64>
    + StaticCast<Self>
{
    fn carry_add(&mut self, rhs: Self, carry: Self) -> Self;
    fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self;
    fn widening_mul(&self, rhs: Self) -> (Self, Self);
}

impl Integer for u8 {
    fn carry_add(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn widening_mul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u16) * (rhs as u16);
        (res as Self, (res >> Self::BITS) as Self)
    }
}

impl Integer for u16 {
    fn carry_add(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn widening_mul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u32) * (rhs as u32);
        (res as Self, (res >> Self::BITS) as Self)
    }
}

impl Integer for u32 {
    fn carry_add(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn widening_mul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u64) * (rhs as u64);
        (res as Self, (res >> Self::BITS) as Self)
    }
}

impl Integer for u64 {
    fn carry_add(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn widening_mul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u128) * (rhs as u128);
        (res as Self, (res >> Self::BITS) as Self)
    }
}

impl Integer for usize {
    fn carry_add(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn widening_mul(&self, rhs: Self) -> (Self, Self) {
        let res = (*self as u128) * (rhs as u128);
        (res as Self, (res >> Self::BITS) as Self)
    }
}

impl Integer for u128 {
    fn carry_add(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_add(rhs);
        let (v2, c2) = v1.overflowing_add(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self {
        let (v1, c1) = self.overflowing_sub(rhs);
        let (v2, c2) = v1.overflowing_sub(carry);
        *self = v2;
        (c1 || c2) as Self
    }

    fn widening_mul(&self, rhs: Self) -> (Self, Self) {
        let a = self * rhs;
        let b = (self >> 64) * rhs;
        let c = self * (rhs >> 64);
        let d = (self >> 64) * (rhs >> 64);
        (d + (c >> 64) + (b >> 64), a)
    }
}

pub trait IArray<I: Integer> {
    fn int_len(&self) -> usize;

    fn get_int(&self, idx: usize) -> Option<I>;
}

pub trait IArrayMut<I: Integer>: IArray<I> {
    fn set_int(&mut self, idx: usize, v: I) -> Option<I>;
}

#[cfg(not(any(target_endian = "big", target_endian = "little")))]
compile_error!("Unknown target endianness");

#[cfg(target_endian = "little")]
impl<I1: Integer, I2: Integer> IArray<I2> for [I1]
where
    I1: StaticCast<I2>,
{
    fn int_len(&self) -> usize {
        (size_of_val(self) + size_of::<I2>() - 1) / size_of::<I2>()
    }

    fn get_int(&self, idx: usize) -> Option<I2> {
        // The conditional check should be optimized during specialization.
        // These asserts should be validated by our tests.
        if size_of::<I1>() >= size_of::<I2>() {
            unsafe {
                debug_assert!(size_of::<I1>() % size_of::<I2>() == 0);
                debug_assert!(align_of::<I1>() % align_of::<I2>() == 0);
                let (head, mid, tail) = self.align_to::<I2>();
                debug_assert!(head.is_empty() && tail.is_empty());
                if idx < mid.len() {
                    Some(mid[idx])
                } else {
                    None
                }
            }
        } else {
            debug_assert!(size_of::<I2>() % size_of::<I1>() == 0);
            let s = size_of::<I2>() / size_of::<I1>();
            let mut v = I2::ZERO;
            if idx >= IArray::<I2>::int_len(self) {
                return None;
            }
            for i in 0..s {
                v |= StaticCast::<I2>::cast_to(*self.get(idx * s + i).unwrap_or(&I1::ZERO))
                    << (size_of::<I1>() * 8 * i);
            }
            Some(v)
        }
    }
}

#[cfg(target_endian = "little")]
impl<I1: Integer, I2: Integer> IArrayMut<I2> for [I1]
where
    I1: StaticCast<I2>,
{
    fn set_int(&mut self, idx: usize, v: I2) -> Option<I2> {
        // The conditional check should be optimized during specialization.
        // These asserts should be validated by our tests.
        if size_of::<I1>() >= size_of::<I2>() {
            unsafe {
                debug_assert!(size_of::<I1>() % size_of::<I2>() == 0);
                debug_assert!(align_of::<I1>() % align_of::<I2>() == 0);
                let (head, mid, tail) = self.align_to_mut::<I2>();
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
            debug_assert!(size_of::<I2>() % size_of::<I1>() == 0);
            let s = size_of::<I2>() / size_of::<I1>();
            let mut old = I2::ZERO;
            if idx >= IArray::<I2>::int_len(self) {
                return None;
            }
            for i in 0..s {
                if let Some(p) = self.get_mut(idx * s + i) {
                    old |= StaticCast::<I2>::cast_to(*p) << (size_of::<I1>() * 8 * i);
                    *p = StaticCast::<I2>::cast_from(v >> (size_of::<I1>() * 8 * i));
                }
            }
            Some(old)
        }
    }
}

// TODO: Big Endian support for IArray and IArrayMut
#[cfg(target_endian = "big")]
compile_error!("Big endian not yet supported");
