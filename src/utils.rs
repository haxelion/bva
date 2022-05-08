use std::fmt::{Debug, Display};
use std::mem::size_of;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, 
    Div, DivAssign, Mul, MulAssign, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

use crate::Bit;

pub trait StaticCast<U> {
    fn cast_from(u: U) -> Self;
    fn cast_to(self) -> U;
}

macro_rules! impl_staticcast {
    ($($type:ty),+) => {
        impl_staticcast!(@as_dual {$($type),+}, {$($type),+});
    };
    (@as_dual {$($lhs:ty),+}, $rhs:tt) => {
        $(
            impl_staticcast!(@as_single $lhs, $rhs);
        )+
    };
    (@as_single $lhs:ty, {$($rhs:ty),+}) => {
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


pub trait Integer : Add<Output=Self> + AddAssign + BitAnd<Output=Self> + BitAndAssign +
    BitOr<Output=Self> + BitOrAssign + BitXor<Output=Self> + BitXorAssign + Constants + Copy + 
    Debug + Div<Output=Self> + DivAssign + Display + Eq + From<Bit> + Into<Bit> + 
    Mul<Output=Self> + MulAssign+ Not<Output=Self> + Ord + PartialEq + PartialOrd + 
    Shl<usize, Output=Self> + ShlAssign<usize> + Shr<usize, Output=Self> + ShrAssign<usize> + 
    Sub<Output=Self> + SubAssign + Sized + StaticCast<u8> {
        fn carry_add(&mut self, rhs: Self, carry: Self) -> Self;
        fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self;
    }

macro_rules! impl_integer {
    ($($type:ty),+) => {
        $(
            impl Integer for $type {
                fn carry_add(&mut self, rhs: Self, carry: Self) -> Self {
                    let (v1, c1) = self.overflowing_add(rhs);
                    let (v2, c2) = v1.overflowing_add(carry);
                    *self = v2;
                    return (c1 || c2) as Self;
                }

                fn carry_sub(&mut self, rhs: Self, carry: Self) -> Self {
                    let (v1, c1) = self.overflowing_sub(rhs);
                    let (v2, c2) = v1.overflowing_sub(carry);
                    *self = v2;
                    return (c1 || c2) as Self;
                }
            }
        )+
    }
}

impl_integer!(u8, u16, u32, u64, u128, usize);

pub trait IArray<I: Integer> {
    fn len(&self) -> usize;

    fn get(&self, idx: usize) -> Option<I>;
}

pub trait IArrayMut<I: Integer> : IArray<I> {
    fn set(&mut self, idx: usize, v: I) -> Option<I>;
}

#[cfg(not(any(target_endian = "big", target_endian = "little")))]
compile_error!("Unknown target endianness");


#[cfg(target_endian = "little")]
impl<I1: Integer, I2: Integer> IArray<I2> for [I1]
    where I2: StaticCast<I1>
{
    fn len(&self) -> usize {
        (self.len() * size_of::<I1>() + size_of::<I2>() - 1) / size_of::<I2>()
    }

    fn get(&self, idx: usize) -> Option<I2> {
        unsafe {
            let (head, mid, tail) = self.align_to::<I2>();
            assert!(head.len() == 0, "unexpected unaligned memory");
            if idx < mid.len() {
                return Some(mid[idx]);
            }
            else if tail.len() > 0 && idx == mid.len() {
                let mut v = I2::ZERO;
                for i in 0..tail.len() {
                    v |= I2::cast_from(tail[i] << (size_of::<I1>() * 8 * i));
                }
                return Some(v);
            }
            else {
                return None;
            }
        }
    }
}

#[cfg(target_endian = "little")]
impl<I1: Integer, I2: Integer> IArrayMut<I2> for [I1]
    where I1: StaticCast<I2>,
          I2: StaticCast<I1>
{
    fn set(&mut self, idx: usize, v: I2) -> Option<I2> {
        unsafe {
            let (head, mid, tail) = self.align_to_mut::<I2>();
            assert!(head.len() == 0, "unexpected unaligned memory");
            if idx < mid.len() {
                let old = mid[idx];
                mid[idx] = v;
                return Some(old);
            }
            else if tail.len() > 0 && idx == mid.len() {
                let mut old = I2::ZERO;
                for i in 0..tail.len() {
                    old |= I2::cast_from(tail[i] << (size_of::<I1>() * 8 * i));
                    tail[i] = I1::cast_from(v >> (size_of::<I1>() * 8 * i));
                }
                return Some(old);
            }
            else {
                return None;
            }
        }
    }
}


// FIXME: Big Endian support for IArray and IArrayMut
#[cfg(target_endian = "big")]
compile_error!("Big endian not yet supported");