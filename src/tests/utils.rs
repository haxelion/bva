use std::mem::size_of;

use crate::utils::{IArray, IArrayMut, Integer, StaticCast};

macro_rules! test_type_combination {
    ($func:ident, $types:tt, $size:tt) => {
        test_type_combination!(@1 $func, $types, $types, $size);
    };
    //(@1 $func:ident, $i1:tt, $i2:tt, {$($size:literal),+}) => {
    (@1 $func:ident, {$($i1:ty),+}, $i2:tt, $size:tt) => {
        $(
            test_type_combination!(@2 $func, $i1, $i2, $size);
        )+
    };
    //(@2 $func:ident, {$($i1:ty),+}, $i2:tt, $size:literal) => {
    (@2 $func:ident, $i1:ty, {$($i2:ty),+}, $size:tt) => {
        $(
            test_type_combination!(@3 $func, $i1, $i2, $size);
        )+
    };
    //(@3 $func:ident, $i1:ty, {$($i2:ty),+}, $size:literal) => {
    (@3 $func:ident, $i1:ty, $i2:ty, {$($size:literal),+}) => {
        $(
            $func::<$i1, $i2, $size>();
        )+
    };
}

fn istream_len_inner<I1: Integer, I2: Integer, const N1: usize>()
where
    I1: StaticCast<I1>,
    I1: StaticCast<I2>,
{
    let array = [I1::ZERO; N1];
    let byte_len = size_of::<I1>() * N1;
    let n2 = (byte_len + size_of::<I2>() - 1) / size_of::<I2>();

    assert_eq!(N1, IArray::<I1>::int_len(array.as_ref()));
    assert_eq!(n2, IArray::<I2>::int_len(array.as_ref()));
    assert_eq!(None, IArray::<I1>::get_int(array.as_ref(), N1));
    assert_eq!(None, IArray::<I2>::get_int(array.as_ref(), n2));
    for i in 0..N1 {
        assert_eq!(IArray::<I1>::get_int(array.as_ref(), i), Some(I1::ZERO));
    }
    for i in 0..n2 {
        assert_eq!(IArray::<I2>::get_int(array.as_ref(), i), Some(I2::ZERO));
    }
}

#[test]
fn istream_len() {
    test_type_combination!(istream_len_inner, {u8, u16, u32, u64, u128, usize}, {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16});
}

fn istream_get_set_inner<I1: Integer, I2: Integer, const N1: usize>()
where
    I1: StaticCast<I1>,
    I1: StaticCast<I2>,
    I2: StaticCast<I1>,
    I2: StaticCast<usize>,
{
    let mut array = [I1::ZERO; N1];
    for i in 0..IArray::<I2>::int_len(array.as_ref()) {
        assert_eq!(
            IArrayMut::<I2>::set_int(array.as_mut(), i, I2::cast_from(i)),
            Some(I2::ZERO)
        );
    }
    for i in 0..IArray::<I2>::int_len(array.as_ref()) {
        assert_eq!(
            IArray::<I2>::get_int(array.as_ref(), i),
            Some(I2::cast_from(i))
        );
    }
}

#[test]
fn istream_get_set() {
    test_type_combination!(istream_get_set_inner, {u8, u16, u32, u64, u128, usize}, {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16});
}
