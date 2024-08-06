use std::cmp::{Ordering, PartialEq, PartialOrd};
use std::ops::{Not, Sub};

use crate::auto::BV;
use crate::bit::Bit;
use crate::dynamic::BVD;
use crate::fixed::BVF;
use crate::tests::{bvf_bvf_inner_unroll, bvf_inner_unroll, random_bv};
use crate::utils::{Integer, StaticCast};
use crate::BitVector;

fn eq_inner<B1, B2>(max_capacity: usize)
where
    B1: BitVector + PartialEq<B2> + Not<Output = B1>,
    B2: BitVector + PartialEq<B1> + for<'a> TryFrom<&'a B1, Error: std::fmt::Debug>,
{
    for length in 1..max_capacity {
        let mut bv1 = random_bv::<B1>(length);
        let mut bv2 = B2::try_from(&bv1).unwrap();
        bv1.resize(max_capacity, Bit::Zero);
        bv2.resize(bv2.significant_bits(), Bit::Zero);
        assert_eq!(bv1, bv2);
        assert_eq!(bv2, bv1);
        assert_ne!(!bv1, bv2);
    }
}

fn eq_inner_bvf_bvf<I1: Integer, I2: Integer, const N1: usize, const N2: usize>()
where
    I1: StaticCast<I2>,
    I2: StaticCast<I1>,
{
    eq_inner::<BVF<I1, N1>, BVF<I2, N2>>(usize::min(
        BVF::<I1, N1>::capacity(),
        BVF::<I2, N2>::capacity(),
    ));
}

fn eq_inner_bvf_bvd<I: Integer, const N: usize>()
where
    I: StaticCast<u64>,
    u64: StaticCast<I>,
{
    eq_inner::<BVF<I, N>, BVD>(BVF::<I, N>::capacity());
    eq_inner::<BVD, BVF<I, N>>(BVF::<I, N>::capacity());
}

fn eq_inner_bvf_bv<I: Integer, const N: usize>()
where
    I: StaticCast<u64>,
    u64: StaticCast<I>,
{
    eq_inner::<BVF<I, N>, BV>(BVF::<I, N>::capacity());
    eq_inner::<BV, BVF<I, N>>(BVF::<I, N>::capacity());
}

#[test]
fn eq_bvf_bvf() {
    bvf_bvf_inner_unroll!(eq_inner_bvf_bvf, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn eq_bvf_bvd() {
    bvf_inner_unroll!(eq_inner_bvf_bvd, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn eq_bvf_bv() {
    bvf_inner_unroll!(eq_inner_bvf_bv, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn eq_bvd_bvd() {
    eq_inner::<BVD, BVD>(512);
}

#[test]
fn eq_bvd_bv() {
    eq_inner::<BVD, BV>(512);
    eq_inner::<BV, BVD>(512);
}

#[test]
fn eq_bv_bv() {
    eq_inner::<BV, BV>(512);
}

fn cmp_inner<B1, B2>(max_capacity: usize)
where
    B1: BitVector + PartialOrd<B2>,
    for<'a, 'b> &'a B1: Sub<&'b B2, Output = B1>,
    B2: BitVector + PartialOrd<B1> + for<'a> TryFrom<&'a B1, Error: std::fmt::Debug>,
    for<'a, 'b> &'a B2: Sub<&'b B1, Output = B2>,
{
    for length in 0..max_capacity {
        let mut bv1 = random_bv::<B1>(length);
        let mut bv2 = random_bv::<B2>(length);
        bv1.resize(max_capacity, Bit::Zero);
        bv2.resize(bv2.significant_bits(), Bit::Zero);
        match bv1.partial_cmp(&bv2).unwrap() {
            Ordering::Less => {
                assert_eq!(bv2.partial_cmp(&bv1).unwrap(), Ordering::Greater);
                let diff = &bv2 - &bv1;
                // If bv1 < bv2, then bv2 - bv1 > 0 and so it shouldn't overflow
                assert_ne!(diff.partial_cmp(&bv2).unwrap(), Ordering::Greater);
            }
            Ordering::Equal => {
                assert_eq!(bv2.partial_cmp(&bv1).unwrap(), Ordering::Equal);
                let diff = &bv2 - &bv1;
                assert!(diff.is_zero());
            }
            Ordering::Greater => {
                assert_eq!(bv2.partial_cmp(&bv1).unwrap(), Ordering::Less);
                let diff = &bv1 - &bv2;
                // If bv1 > bv2, then bv1 - bv2 > 0 and so it shouldn't overflow
                assert_ne!(diff.partial_cmp(&bv1).unwrap(), Ordering::Greater);
            }
        }
    }
}

fn cmp_inner_bvf_bvf<I1: Integer, I2: Integer, const N1: usize, const N2: usize>()
where
    I1: StaticCast<I2>,
    I2: StaticCast<I1>,
{
    cmp_inner::<BVF<I1, N1>, BVF<I2, N2>>(usize::min(
        BVF::<I1, N1>::capacity(),
        BVF::<I2, N2>::capacity(),
    ));
}

fn cmp_inner_bvf_bvd<I: Integer, const N: usize>()
where
    I: StaticCast<u64>,
    u64: StaticCast<I>,
{
    cmp_inner::<BVF<I, N>, BVD>(BVF::<I, N>::capacity());
    cmp_inner::<BVD, BVF<I, N>>(BVF::<I, N>::capacity());
}

fn cmp_inner_bvf_bv<I: Integer, const N: usize>()
where
    I: StaticCast<u64>,
    u64: StaticCast<I>,
{
    cmp_inner::<BVF<I, N>, BV>(BVF::<I, N>::capacity());
    cmp_inner::<BV, BVF<I, N>>(BVF::<I, N>::capacity());
}

#[test]
fn cmp_bvf_bvf() {
    bvf_bvf_inner_unroll!(cmp_inner_bvf_bvf, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn cmp_bvf_bvd() {
    bvf_inner_unroll!(cmp_inner_bvf_bvd, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn cmp_bvf_bv() {
    bvf_inner_unroll!(cmp_inner_bvf_bv, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn cmp_bvd_bvd() {
    cmp_inner::<BVD, BVD>(512);
}

#[test]
fn cmp_bvd_bv() {
    cmp_inner::<BVD, BV>(512);
    cmp_inner::<BV, BVD>(512);
}

#[test]
fn cmp_bv_bv() {
    cmp_inner::<BV, BV>(512);
}
