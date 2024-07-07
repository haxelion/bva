mod and {
    use std::ops::{BitAnd, BitAndAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(BitAnd::bitand, BitAndAssign::bitand_assign, {
        op_test_block
    });
}

mod not {
    use crate::auto::BV;
    use crate::dynamic::BVD;
    use crate::fixed::BVF;
    use crate::tests::{bvf_inner_unroll, random_test_bv};
    use crate::utils::Integer;

    fn bvf_test_inner<I: Integer, const N: usize>() {
        for size in 0..BVF::<I, N>::capacity() {
            let (bv, bi) = random_test_bv::<BVF<I, N>>(size);
            assert_eq!(!&bv, !&bi);
            assert_eq!(!bv, !bi);
        }
    }

    #[test]
    fn bvf() {
        bvf_inner_unroll!(bvf_test_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
    }

    #[test]
    fn bvd() {
        for size in 0..512 {
            let (bv, bi) = random_test_bv::<BVD>(size);
            assert_eq!(!&bv, !&bi);
            assert_eq!(!bv, !bi);
        }
    }

    #[test]
    fn bv() {
        for size in 0..512 {
            let (bv, bi) = random_test_bv::<BV>(size);
            assert_eq!(!&bv, !&bi);
            assert_eq!(!bv, !bi);
        }
    }
}

mod or {
    use std::ops::{BitOr, BitOrAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(BitOr::bitor, BitOrAssign::bitor_assign, { op_test_block });
}

mod shift {
    use std::ops::{Shl, ShlAssign, Shr, ShrAssign};

    use num_bigint::BigInt;
    use rand::random;

    use crate::auto::BV;
    use crate::dynamic::BVD;
    use crate::fixed::BVF;
    use crate::tests::{bvf_inner_unroll, random_test_bv, shift_test_block};
    use crate::utils::Integer;

    fn shl_bvf_inner<I: Integer, const N: usize>() {
        for size in 1..BVF::<I, N>::capacity() {
            shift_test_block!(BVF<I, N>, {u8, u16, u32, u64, u128, usize}, Shl::shl, ShlAssign::shl_assign, size);
        }
    }

    #[test]
    fn shl_bvf() {
        bvf_inner_unroll!(shl_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
    }

    #[test]
    fn shl_bvd() {
        for size in 1..512 {
            shift_test_block!(BVD, {u8, u16, u32, u64, u128, usize}, Shl::shl, ShlAssign::shl_assign, size);
        }
    }

    #[test]
    fn shl_bv() {
        for size in 1..512 {
            shift_test_block!(BV, {u8, u16, u32, u64, u128, usize}, Shl::shl, ShlAssign::shl_assign, size);
        }
    }

    fn shr_bvf_inner<I: Integer, const N: usize>() {
        for size in 1..BVF::<I, N>::capacity() {
            shift_test_block!(BVF<I, N>, {u8, u16, u32, u64, u128, usize}, Shr::shr, ShrAssign::shr_assign, size);
        }
    }

    #[test]
    fn shr_bvf() {
        bvf_inner_unroll!(shr_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
    }

    #[test]
    fn shr_bvd() {
        for size in 1..512 {
            shift_test_block!(BVD, {u8, u16, u32, u64, u128, usize}, Shr::shr, ShrAssign::shr_assign, size);
        }
    }

    #[test]
    fn shr_bv() {
        for size in 1..512 {
            shift_test_block!(BV, {u8, u16, u32, u64, u128, usize}, Shr::shr, ShrAssign::shr_assign, size);
        }
    }
}

mod xor {
    use std::ops::{BitXor, BitXorAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(BitXor::bitxor, BitXorAssign::bitxor_assign, {
        op_test_block
    });
}
