use num_bigint::BigInt;
use rand::random;

use crate::auto::BV;
use crate::dynamic::BVD;
use crate::fixed::BVF;
use crate::utils::Integer;
use crate::{Bit, BitVector};

mod arithmetic;
mod binary;
mod bitvector;
mod conversion;
mod formatting;
mod iter;
mod utils;

fn random_bv<B: BitVector>(length: usize) -> B {
    let mut bv = B::zeros(length);
    for i in 0..length {
        bv.set(i, Bit::from(random::<bool>()));
    }
    bv
}

fn random_test_bv<B: BitVector>(length: usize) -> (B, BigInt) {
    let bv: B = random_bv(length);
    let mut bi = BigInt::from(0u8);
    for i in 0..bv.len() {
        bi.set_bit(i as u64, bv.get(i).into());
    }
    (bv, bi)
}

impl<I1: Integer, const N: usize> PartialEq<BigInt> for BVF<I1, N> {
    fn eq(&self, other: &BigInt) -> bool {
        for i in 0..self.len() {
            if self.get(i) != Bit::from(other.bit(i as u64)) {
                return false;
            }
        }
        true
    }
}

impl PartialEq<BigInt> for BVD {
    fn eq(&self, other: &BigInt) -> bool {
        for i in 0..self.len() {
            if self.get(i) != Bit::from(other.bit(i as u64)) {
                return false;
            }
        }
        true
    }
}

impl PartialEq<BigInt> for BV {
    fn eq(&self, other: &BigInt) -> bool {
        for i in 0..self.len() {
            if self.get(i) != Bit::from(other.bit(i as u64)) {
                return false;
            }
        }
        true
    }
}

macro_rules! bvf_inner_unroll {
    ($func:ident, {$($lhs:ty),+}, $sl:tt) => {
        $(
            bvf_inner_unroll!($func, $lhs, $sl);
        )+
    };
    ($func:ident, $lhs:ty, {$($sl:literal),+}) => {
        $(
            $func::<$lhs, $sl>();
        )+
    };
}

macro_rules! bvf_inner_unroll_cap {
    ($func:ident, {$($lhs:ty),+}, $sl:tt) => {
        $(
            bvf_inner_unroll_cap!($func, $lhs, $sl);
        )+
    };
    ($func:ident, $lhs:ty, {$($sl:literal),+}) => {
        $(
            $func::<BVF<$lhs, $sl>>(BVF::<$lhs, $sl>::capacity());
        )+
    };
}

macro_rules! bvf_bvf_inner_unroll {
    ($func:ident, $types:tt, $sizes:tt) => {
        bvf_bvf_inner_unroll!($func, $types, $types, $sizes, $sizes);
    };
    ($func:ident, {$($lhs:ty),+}, $rhs:tt, $sl:tt, $sr:tt) => {
        $(
            bvf_bvf_inner_unroll!($func, $lhs, $rhs, $sl, $sr);
        )+
    };
    ($func:ident, $lhs:ty, {$($rhs:ty),+}, $sl:tt, $sr:tt) => {
        $(
            bvf_bvf_inner_unroll!($func, $lhs, $rhs, $sl, $sr);
        )+
    };
    ($func:ident, $lhs:ty, $rhs:ty, {$($sl:literal),+}, $sr:tt) => {
        $(
            bvf_bvf_inner_unroll!($func, $lhs, $rhs, $sl, $sr);
        )+
    };
    ($func:ident, $lhs:ty, $rhs:ty, $sl:literal, {$($sr:literal),+}) => {
        $(
            $func::<$lhs, $rhs, $sl, $sr>();
        )+
    };
}

macro_rules! op_test_block {
    ($lhs:ty, $rhs:ty, $op:path, $op_assign:path, $size:ident) => {
        let modulo = BigInt::from(1u8) << $size;
        let (bv1, bi1) = random_test_bv::<$lhs>($size);
        let (bv2, bi2) = random_test_bv::<$rhs>($size);
        let reference = $op(&bi1, &bi2) % &modulo;
        // Normal op
        assert_eq!($op(&bv1, &bv2), reference);
        assert_eq!($op(bv1.clone(), &bv2), reference);
        assert_eq!($op(&bv1, bv2.clone()), reference);
        assert_eq!($op(bv1.clone(), bv2.clone()), reference);
        // Assign op
        let mut bv3 = bv1.clone();
        $op_assign(&mut bv3, &bv2);
        assert_eq!(bv3, reference);
        bv3 = bv1.clone();
        $op_assign(&mut bv3, bv2);
        assert_eq!(bv3, reference);
    };
}

macro_rules! op_test_section {
    ($op:path, $op_assign:path) => {
        fn bvf_bvf_inner<
            I1: Integer + StaticCast<I2>,
            I2: Integer + StaticCast<I1>,
            const N1: usize,
            const N2: usize,
        >() {
            for size in 1..usize::min(BVF::<I1, N1>::capacity(), BVF::<I2, N2>::capacity()) {
                op_test_block!(BVF<I1, N1>, BVF<I2, N2>, $op, $op_assign, size);
            }
        }

        #[test]
        fn bvf_bvf() {
            bvf_bvf_inner_unroll!(bvf_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
        }

        fn bvf_bvd_inner<I: Integer, const N: usize>()
        where
            u64: StaticCast<I>,
        {
            for size in 1..BVF::<I, N>::capacity() {
                op_test_block!(BVF<I, N>, BVD, $op, $op_assign, size);
                op_test_block!(BVD, BVF<I, N>, $op, $op_assign, size);
            }
        }

        #[test]
        fn bvf_bvd() {
            bvf_inner_unroll!(bvf_bvd_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
        }

        fn bvf_bv_inner<I: Integer, const N: usize>()
        where
            u64: StaticCast<I>,
        {
            for size in 1..BVF::<I, N>::capacity() {
                op_test_block!(BVF<I, N>, BV, $op, $op_assign, size);
                op_test_block!(BV, BVF<I, N>, $op, $op_assign, size);
            }
        }

        #[test]
        fn bvf_bv() {
            bvf_inner_unroll!(bvf_bv_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
        }

        #[test]
        fn bvd_bvd() {
            for size in 1..512 {
                op_test_block!(BVD, BVD, $op, $op_assign, size);
            }
        }

        #[test]
        fn bvd_bv() {
            for size in 1..512 {
                op_test_block!(BVD, BV, $op, $op_assign, size);
                op_test_block!(BV, BVD, $op, $op_assign, size);
            }
        }

        #[test]
        fn bv_bv() {
            for size in 1..512 {
                op_test_block!(BV, BV, $op, $op_assign, size);
            }
        }
    };
}

pub(crate) use bvf_bvf_inner_unroll;
pub(crate) use bvf_inner_unroll;
pub(crate) use bvf_inner_unroll_cap;
pub(crate) use op_test_block;
pub(crate) use op_test_section;
