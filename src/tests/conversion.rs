use std::fmt::Debug;

use crate::auto::BV;
use crate::dynamic::BVD;
use crate::fixed::BVF;
use crate::tests::{bvf_bvf_inner_unroll, bvf_inner_unroll, random_test_bv};
use crate::utils::{Integer, StaticCast};
use crate::BitVector;

use num_bigint::BigInt;

fn from_inner<B: BitVector, C: for<'a> From<&'a B> + PartialEq<BigInt> + PartialEq<B> + Debug>(
    capacity: usize,
) {
    for size in 1..capacity {
        let (bv, bi) = random_test_bv::<B>(size);
        let cv = C::from(&bv);
        assert_eq!(cv, bv);
        assert_eq!(cv, bi);
    }
}

fn try_from_inner<B, C>(capacity: usize)
where
    B: BitVector,
    C: for<'a> TryFrom<&'a B> + PartialEq<BigInt> + PartialEq<B> + Debug,
    for<'a> <C as TryFrom<&'a B>>::Error: Debug,
{
    for size in 1..capacity {
        let (bv, bi) = random_test_bv::<B>(size);
        let cv = C::try_from(&bv).unwrap();
        assert_eq!(cv, bv);
        assert_eq!(cv, bi);
    }
}

fn try_from_int_inner<B, C>(capacity: usize)
where
    B: BitVector + TryFrom<C>,
    C: Integer + for<'a> TryFrom<&'a B> + Debug,
    for<'a> <C as TryFrom<&'a B>>::Error: Debug,
    <B as TryFrom<C>>::Error: Debug,
{
    for size in 1..capacity {
        let (bv, _) = random_test_bv::<B>(size);
        let c = C::try_from(&bv).unwrap();
        let bv2 = B::try_from(c).unwrap();
        assert_eq!(bv2, bv);
    }
}

fn try_from_bvf_int_inner<I: Integer, const N: usize>() {
    try_from_int_inner::<BVF<I, N>, u8>(usize::min(BVF::<I, N>::capacity(), u8::BITS as usize));
    try_from_int_inner::<BVF<I, N>, u16>(usize::min(BVF::<I, N>::capacity(), u16::BITS as usize));
    try_from_int_inner::<BVF<I, N>, u32>(usize::min(BVF::<I, N>::capacity(), u32::BITS as usize));
    try_from_int_inner::<BVF<I, N>, u64>(usize::min(BVF::<I, N>::capacity(), u64::BITS as usize));
    try_from_int_inner::<BVF<I, N>, u128>(usize::min(BVF::<I, N>::capacity(), u128::BITS as usize));
}

fn try_from_bvf_bvf_inner<I1, I2, const N1: usize, const N2: usize>()
where
    I1: Integer + StaticCast<I2>,
    I2: Integer + StaticCast<I1>,
{
    try_from_inner::<BVF<I1, N1>, BVF<I2, N2>>(usize::min(
        BVF::<I1, N1>::capacity(),
        BVF::<I2, N2>::capacity(),
    ));
}

fn try_from_bvf_bvd_inner<I: Integer, const N: usize>()
where
    u64: StaticCast<I>,
{
    try_from_inner::<BVF<I, N>, BVD>(BVF::<I, N>::capacity());
}

fn try_from_bvf_bv_inner<I: Integer, const N: usize>()
where
    u64: StaticCast<I>,
{
    try_from_inner::<BVF<I, N>, BV>(BVF::<I, N>::capacity());
}

fn try_from_bvd_bvf_inner<I: Integer, const N: usize>()
where
    u64: StaticCast<I>,
{
    try_from_inner::<BVD, BVF<I, N>>(BVF::<I, N>::capacity());
}

fn try_from_bv_bvf_inner<I: Integer, const N: usize>()
where
    u64: StaticCast<I>,
{
    try_from_inner::<BV, BVF<I, N>>(BVF::<I, N>::capacity());
}

#[test]
fn from_bvf_int() {
    bvf_inner_unroll!(try_from_bvf_int_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_bvf_bvf() {
    bvf_bvf_inner_unroll!(try_from_bvf_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_bvf_bvd() {
    bvf_inner_unroll!(try_from_bvf_bvd_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_bvf_bv() {
    bvf_inner_unroll!(try_from_bvf_bv_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_bvd_int() {
    try_from_int_inner::<BVD, u8>(u8::BITS as usize);
    try_from_int_inner::<BVD, u16>(u16::BITS as usize);
    try_from_int_inner::<BVD, u32>(u32::BITS as usize);
    try_from_int_inner::<BVD, u64>(u64::BITS as usize);
    try_from_int_inner::<BVD, u128>(u128::BITS as usize);
}

#[test]
fn from_bvd_bvf() {
    bvf_inner_unroll!(try_from_bvd_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_bvd_bv() {
    from_inner::<BVD, BV>(512);
}

#[test]
fn from_bv_int() {
    try_from_int_inner::<BV, u8>(u8::BITS as usize);
    try_from_int_inner::<BV, u16>(u16::BITS as usize);
    try_from_int_inner::<BV, u32>(u32::BITS as usize);
    try_from_int_inner::<BV, u64>(u64::BITS as usize);
    try_from_int_inner::<BV, u128>(u128::BITS as usize);
}

#[test]
fn from_bv_bvf() {
    bvf_inner_unroll!(try_from_bv_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_bv_bvd() {
    from_inner::<BV, BVD>(512);
}
