use std::fmt::{Debug, Display};
use std::mem::{align_of, size_of};
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, 
    Div, DivAssign, Mul, MulAssign, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

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


pub trait Integer : Add<Output=Self> + AddAssign + BitAnd<Output=Self> + BitAndAssign +
    BitOr<Output=Self> + BitOrAssign + BitXor<Output=Self> + BitXorAssign + Constants + Copy + 
    Debug + Div<Output=Self> + DivAssign + Display + Eq + From<Bit> + Into<Bit> + 
    Mul<Output=Self> + MulAssign+ Not<Output=Self> + Ord + PartialEq + PartialOrd + 
    Shl<usize, Output=Self> + ShlAssign<usize> + Shr<usize, Output=Self> + ShrAssign<usize> + 
    Sub<Output=Self> + SubAssign + Sized + StaticCast<u8> + StaticCast<u64> + StaticCast<Self> {
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

pub trait IArray<I1: Integer> {
    fn int_len<I2: Integer>(&self) -> usize;

    fn get_int<I2: Integer>(&self, idx: usize) -> Option<I2> where I1: StaticCast<I2>;
}

pub trait IArrayMut<I1: Integer> : IArray<I1> {
    fn set_int<I2: Integer>(&mut self, idx: usize, v: I2) -> Option<I2> where I1: StaticCast<I2>;
}

#[cfg(not(any(target_endian = "big", target_endian = "little")))]
compile_error!("Unknown target endianness");


#[cfg(target_endian = "little")]
impl<I1: Integer> IArray<I1> for [I1] {
    fn int_len<I2: Integer>(&self) -> usize {
        (self.len() * size_of::<I1>() + size_of::<I2>() - 1) / size_of::<I2>()
    }

    fn get_int<I2: Integer>(&self, idx: usize) -> Option<I2> where I1: StaticCast<I2> {
        // The conditional check should be optimized during specialization.
        // These asserts should be validated by our tests.
        if size_of::<I1>() >= size_of::<I2>() {
            unsafe {
                debug_assert!(size_of::<I1>() % size_of::<I2>() == 0);
                debug_assert!(align_of::<I1>() % align_of::<I2>() == 0);
                let (head, mid, tail) = self.align_to::<I2>();
                debug_assert!(head.len() == 0 && tail.len() == 0);
                if idx < mid.len() {
                    return Some(mid[idx]);
                }
                else {
                    return None;
                }
            }
        }
        else {
            debug_assert!(size_of::<I2>() % size_of::<I1>() == 0);
            let s = size_of::<I2>() / size_of::<I1>();
            let mut v = I2::ZERO;
            if idx >= self.int_len::<I2>() {
                return None;
            }
            for i in 0..s {
                v |= StaticCast::<I2>::cast_to(*self.get(idx * s + i).unwrap_or(&I1::ZERO)) << (size_of::<I1>() * 8 * i);
            }
            return Some(v);
        }
    }
}

#[cfg(target_endian = "little")]
impl<I1: Integer> IArrayMut<I1> for [I1]
{
    fn set_int<I2: Integer>(&mut self, idx: usize, v: I2) -> Option<I2> where I1: StaticCast<I2> {
        // The conditional check should be optimized during specialization.
        // These asserts should be validated by our tests.
        if size_of::<I1>() >= size_of::<I2>() {
            unsafe {
                debug_assert!(size_of::<I1>() % size_of::<I2>() == 0);
                debug_assert!(align_of::<I1>() % align_of::<I2>() == 0);
                let (head, mid, tail) = self.align_to_mut::<I2>();
                debug_assert!(head.len() == 0 && tail.len() == 0);
                if idx < mid.len() {
                    let old = mid[idx];
                    mid[idx] = v;
                    return Some(old);
                }
                else {
                    return None;
                }
            }
        }
        else {
            debug_assert!(size_of::<I2>() % size_of::<I1>() == 0);
            let s = size_of::<I2>() / size_of::<I1>();
            let mut old = I2::ZERO;
            if idx >= self.int_len::<I2>() {
                return None;
            }
            for i in 0..s {
                if let Some(p) = self.get_mut(idx * s + i) {
                    old |= StaticCast::<I2>::cast_to(*p) << (size_of::<I1>() * 8 * i);
                    *p = StaticCast::<I2>::cast_from(v >> (size_of::<I1>() * 8 * i));
                }
            }
            return Some(old);
        }
    }
}


// TODO: Big Endian support for IArray and IArrayMut
#[cfg(target_endian = "big")]
compile_error!("Big endian not yet supported");