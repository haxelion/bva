use std::fmt::Debug;

use crate::auto::Bv;
use crate::dynamic::Bvd;
use crate::fixed::Bvf;
use crate::tests::{bvf_bvf_inner_unroll, bvf_inner_unroll, random_bv, random_test_bv};
use crate::utils::{IArray, Integer, StaticCast};
use crate::{BitVector, ConvertionError};

use num_bigint::BigInt;

fn from_inner<B, C>(capacity: usize)
where
    B: BitVector,
    C: From<B> + for<'a> From<&'a B> + PartialEq<BigInt> + PartialEq<B> + Debug,
{
    for size in 1..capacity {
        let (bv, bi) = random_test_bv::<B>(size);
        let cv1 = C::from(&bv);
        let cv2 = C::from(bv);
        assert_eq!(cv1, bi);
        assert_eq!(cv2, bi);
    }
}

fn try_from_inner<B, C>(capacity: usize)
where
    B: BitVector,
    C: TryFrom<B, Error: Debug> + for<'a> TryFrom<&'a B, Error: Debug> + PartialEq<BigInt> + Debug,
{
    for size in 1..capacity {
        let (bv, bi) = random_test_bv::<B>(size);
        let cv1 = C::try_from(&bv).unwrap();
        let cv2 = C::try_from(bv).unwrap();
        assert_eq!(cv1, bi);
        assert_eq!(cv2, bi);
    }
}

fn try_from_uint_inner<B, C>(capacity: usize)
where
    B: BitVector
        + TryFrom<C, Error: Debug>
        + for<'a> TryFrom<&'a C, Error: Debug>
        + PartialEq<BigInt>,
    C: Integer + TryFrom<B, Error: Debug> + for<'a> TryFrom<&'a B, Error: Debug>,
{
    for size in 1..capacity {
        let (bv1, bi) = random_test_bv::<B>(size);
        let c1 = C::try_from(&bv1).unwrap();
        let bv2 = B::try_from(&c1).unwrap();
        assert_eq!(bv2, bi);
        let c2 = C::try_from(bv1).unwrap();
        let bv3 = B::try_from(c2).unwrap();
        assert_eq!(bv3, bi);
    }
}

fn try_from_bvf_uint_inner<I: Integer, const N: usize>()
where
    I: StaticCast<usize>,
{
    try_from_uint_inner::<Bvf<I, N>, u8>(usize::min(Bvf::<I, N>::capacity(), u8::BITS as usize));
    try_from_uint_inner::<Bvf<I, N>, u16>(usize::min(Bvf::<I, N>::capacity(), u16::BITS as usize));
    try_from_uint_inner::<Bvf<I, N>, u32>(usize::min(Bvf::<I, N>::capacity(), u32::BITS as usize));
    try_from_uint_inner::<Bvf<I, N>, u64>(usize::min(Bvf::<I, N>::capacity(), u64::BITS as usize));
    try_from_uint_inner::<Bvf<I, N>, u128>(usize::min(
        Bvf::<I, N>::capacity(),
        u128::BITS as usize,
    ));
    if Bvf::<I, N>::capacity() < u16::BITS as usize {
        assert_eq!(
            Bvf::<I, N>::try_from(u16::MAX),
            Err(ConvertionError::NotEnoughCapacity)
        );
    } else if Bvf::<I, N>::capacity() > u16::BITS as usize {
        assert_eq!(
            u16::try_from(Bvf::<I, N>::ones(u16::BITS as usize + 1)),
            Err(ConvertionError::NotEnoughCapacity)
        );
    }
    if Bvf::<I, N>::capacity() < u32::BITS as usize {
        assert_eq!(
            Bvf::<I, N>::try_from(u32::MAX),
            Err(ConvertionError::NotEnoughCapacity)
        );
    } else if Bvf::<I, N>::capacity() > u32::BITS as usize {
        assert_eq!(
            u32::try_from(Bvf::<I, N>::ones(u32::BITS as usize + 1)),
            Err(ConvertionError::NotEnoughCapacity)
        );
    }
    if Bvf::<I, N>::capacity() < u64::BITS as usize {
        assert_eq!(
            Bvf::<I, N>::try_from(u64::MAX),
            Err(ConvertionError::NotEnoughCapacity)
        );
    } else if Bvf::<I, N>::capacity() > u64::BITS as usize {
        assert_eq!(
            u64::try_from(Bvf::<I, N>::ones(u64::BITS as usize + 1)),
            Err(ConvertionError::NotEnoughCapacity)
        );
    }
    if Bvf::<I, N>::capacity() < usize::BITS as usize {
        assert_eq!(
            Bvf::<I, N>::try_from(usize::MAX),
            Err(ConvertionError::NotEnoughCapacity)
        );
    } else if Bvf::<I, N>::capacity() > usize::BITS as usize {
        assert_eq!(
            usize::try_from(Bvf::<I, N>::ones(usize::BITS as usize + 1)),
            Err(ConvertionError::NotEnoughCapacity)
        );
    }
    if Bvf::<I, N>::capacity() < u128::BITS as usize {
        assert_eq!(
            Bvf::<I, N>::try_from(u128::MAX),
            Err(ConvertionError::NotEnoughCapacity)
        );
    } else if Bvf::<I, N>::capacity() > u128::BITS as usize {
        assert_eq!(
            u128::try_from(Bvf::<I, N>::ones(u128::BITS as usize + 1)),
            Err(ConvertionError::NotEnoughCapacity)
        );
    }
}

#[test]
fn from_bvf_uint() {
    bvf_inner_unroll!(try_from_bvf_uint_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

fn try_from_bvf_bvf_inner<I1, I2, const N1: usize, const N2: usize>()
where
    I1: Integer + StaticCast<I2>,
    I2: Integer + StaticCast<I1>,
{
    for size in 1..usize::min(Bvf::<I1, N1>::capacity(), Bvf::<I2, N2>::capacity()) {
        let (bv, bi) = random_test_bv::<Bvf<I1, N1>>(size);
        let cv1 = Bvf::<I2, N2>::try_from(&bv).unwrap();
        assert_eq!(cv1, bi);
    }
    if Bvf::<I1, N1>::capacity() > Bvf::<I2, N2>::capacity() {
        assert_eq!(
            Bvf::<I2, N2>::try_from(&Bvf::<I1, N1>::ones(Bvf::<I1, N1>::capacity())),
            Err(ConvertionError::NotEnoughCapacity)
        )
    }
}

#[test]
fn from_bvf_bvf() {
    bvf_bvf_inner_unroll!(try_from_bvf_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

fn try_from_bvf_bvd_inner<I: Integer, const N: usize>()
where
    u64: StaticCast<I>,
{
    try_from_inner::<Bvf<I, N>, Bvd>(Bvf::<I, N>::capacity());
    assert_eq!(
        Bvf::<I, N>::try_from(Bvd::ones(Bvf::<I, N>::capacity() + 1)),
        Err(ConvertionError::NotEnoughCapacity)
    );
}

#[test]
fn from_bvf_bvd() {
    bvf_inner_unroll!(try_from_bvf_bvd_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

fn try_from_bvf_bv_inner<I: Integer, const N: usize>()
where
    u64: StaticCast<I>,
{
    try_from_inner::<Bvf<I, N>, Bv>(Bvf::<I, N>::capacity());
    assert_eq!(
        Bvf::<I, N>::try_from(Bv::ones(Bvf::<I, N>::capacity() + 1)),
        Err(ConvertionError::NotEnoughCapacity)
    );
}

#[test]
fn from_bvf_bv() {
    bvf_inner_unroll!(try_from_bvf_bv_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_bvd_uint() {
    try_from_uint_inner::<Bvd, u8>(u8::BITS as usize);
    try_from_uint_inner::<Bvd, u16>(u16::BITS as usize);
    try_from_uint_inner::<Bvd, u32>(u32::BITS as usize);
    try_from_uint_inner::<Bvd, u64>(u64::BITS as usize);
    try_from_uint_inner::<Bvd, u128>(u128::BITS as usize);
    assert_eq!(
        u8::try_from(Bvd::ones(9)),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        u16::try_from(Bvd::ones(17)),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        u32::try_from(Bvd::ones(33)),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        u64::try_from(Bvd::ones(65)),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        u128::try_from(Bvd::ones(129)),
        Err(ConvertionError::NotEnoughCapacity)
    );
}

fn try_from_bvd_bvf_inner<I: Integer, const N: usize>()
where
    u64: StaticCast<I>,
{
    try_from_inner::<Bvd, Bvf<I, N>>(Bvf::<I, N>::capacity());
}

#[test]
fn from_bvd_bvf() {
    bvf_inner_unroll!(try_from_bvd_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

fn try_from_bv_bvf_inner<I: Integer, const N: usize>()
where
    u64: StaticCast<I>,
{
    try_from_inner::<Bv, Bvf<I, N>>(Bvf::<I, N>::capacity());
}

#[test]
fn from_bvd_bv() {
    from_inner::<Bvd, Bv>(512);
}

#[test]
fn from_bv_uint() {
    try_from_uint_inner::<Bv, u8>(u8::BITS as usize);
    try_from_uint_inner::<Bv, u16>(u16::BITS as usize);
    try_from_uint_inner::<Bv, u32>(u32::BITS as usize);
    try_from_uint_inner::<Bv, u64>(u64::BITS as usize);
    try_from_uint_inner::<Bv, u128>(u128::BITS as usize);
    assert_eq!(
        u8::try_from(Bv::ones(9)),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        u16::try_from(Bv::ones(17)),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        u32::try_from(Bv::ones(33)),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        u64::try_from(Bv::ones(65)),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        u128::try_from(Bv::ones(129)),
        Err(ConvertionError::NotEnoughCapacity)
    );
}

#[test]
fn from_bv_bvf() {
    bvf_inner_unroll!(try_from_bv_bvf_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_bv_bvd() {
    from_inner::<Bv, Bvd>(512);
}

fn from_array_inner<B, I>(max_capacity: usize)
where
    <B as IArray>::I: StaticCast<I>,
    B: BitVector + for<'a> TryFrom<&'a [I], Error: Debug>,
    I: Integer,
{
    for length in 0..(max_capacity / I::BITS * I::BITS) {
        let bv1 = random_bv::<B>(length);
        let array: Vec<I> = (0..bv1.int_len::<I>())
            .map(|i| bv1.get_int(i).unwrap())
            .collect();
        let bv2 = B::try_from(&array[..]).unwrap();
        assert_eq!(bv1, bv2);
    }
}

fn from_bvf_array_inner<I: Integer, const N: usize>() {
    from_array_inner::<Bvf<I, N>, u8>(Bvf::<I, N>::capacity());
    from_array_inner::<Bvf<I, N>, u16>(Bvf::<I, N>::capacity());
    from_array_inner::<Bvf<I, N>, u32>(Bvf::<I, N>::capacity());
    from_array_inner::<Bvf<I, N>, u64>(Bvf::<I, N>::capacity());
    from_array_inner::<Bvf<I, N>, u128>(Bvf::<I, N>::capacity());
}

#[test]
fn from_bvf_array() {
    bvf_inner_unroll!(from_bvf_array_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
    assert_eq!(
        Bvf::<u8, 3>::try_from(&[1u16; 2][..]),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        Bvf::<u16, 3>::try_from(&[1u32; 2][..]),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        Bvf::<u32, 3>::try_from(&[1u64; 2][..]),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        Bvf::<u64, 3>::try_from(&[1u128; 2][..]),
        Err(ConvertionError::NotEnoughCapacity)
    );
}

#[test]
fn from_bvd_array() {
    from_array_inner::<Bvd, u8>(256);
    from_array_inner::<Bvd, u16>(256);
    from_array_inner::<Bvd, u32>(256);
    from_array_inner::<Bvd, u64>(256);
    from_array_inner::<Bvd, u128>(256);
}

#[test]
fn from_bv_array() {
    from_array_inner::<Bv, u8>(256);
    from_array_inner::<Bv, u16>(256);
    from_array_inner::<Bv, u32>(256);
    from_array_inner::<Bv, u64>(256);
    from_array_inner::<Bv, u128>(256);
}
