use crate::auto::BV;
use crate::dynamic::BVD;
use crate::fixed::BVF;
use crate::tests::{bvf_inner_unroll_cap, random_test_bv};
use crate::{Bit, BitVector, ConvertionError};

fn display_inner<B: BitVector>(capacity: usize) {
    for size in 1..capacity {
        let (bv, bi) = random_test_bv::<B>(size);
        assert_eq!(format!("{:b}", &bv), format!("{:b}", &bi));
        assert_eq!(format!("{:#b}", &bv), format!("{:#b}", &bi));
        assert_eq!(format!("{:#0200b}", &bv), format!("{:#0200b}", &bi));
        assert_eq!(format!("{:o}", &bv), format!("{:o}", &bi));
        assert_eq!(format!("{:#o}", &bv), format!("{:#o}", &bi));
        assert_eq!(format!("{:#0100o}", &bv), format!("{:#0100o}", &bi));
        assert_eq!(format!("{:x}", &bv), format!("{:x}", &bi));
        assert_eq!(format!("{:#x}", &bv), format!("{:#x}", &bi));
        assert_eq!(format!("{:#050x}", &bv), format!("{:#050x}", &bi));
        assert_eq!(format!("{:X}", &bv), format!("{:X}", &bi));
        assert_eq!(format!("{:#X}", &bv), format!("{:#X}", &bi));
        assert_eq!(format!("{:#050X}", &bv), format!("{:#050X}", &bi));
    }
}

#[test]
fn display_bit() {
    assert_eq!(format!("{}", Bit::Zero), "0");
    assert_eq!(format!("{}", Bit::One), "1");
}

#[test]
fn display_bvf() {
    bvf_inner_unroll_cap!(display_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn display_bvd() {
    display_inner::<BVD>(512);
}

#[test]
fn display_bv() {
    display_inner::<BV>(512);
}

fn from_string_inner<B: BitVector>(capacity: usize) {
    for size in 1..capacity {
        let (bv, bi) = random_test_bv::<B>(size);
        assert_eq!(B::from_binary(&format!("{:b}", &bi)).unwrap(), bv);
        assert_eq!(B::from_binary(&format!("{:b}", &bv)).unwrap(), bv);
        assert_eq!(B::from_hex(&format!("{:x}", &bi)).unwrap(), bv);
        assert_eq!(B::from_hex(&format!("{:x}", &bv)).unwrap(), bv);
        assert_eq!(B::from_hex(&format!("{:X}", &bi)).unwrap(), bv);
        assert_eq!(B::from_hex(&format!("{:X}", &bv)).unwrap(), bv);
    }

    assert_eq!(
        B::from_binary("000x"),
        Err(ConvertionError::InvalidFormat(3))
    );
    assert_eq!(B::from_hex("0t"), Err(ConvertionError::InvalidFormat(1)));
}

#[test]
fn from_string_bvf() {
    bvf_inner_unroll_cap!(from_string_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
    assert_eq!(
        BVF::<u8, 1>::from_binary("0000000001"),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        BVF::<u16, 1>::from_hex("abcde"),
        Err(ConvertionError::NotEnoughCapacity)
    );
}

#[test]
fn from_string_bvd() {
    from_string_inner::<BVD>(512);
}

#[test]
fn from_string_bv() {
    from_string_inner::<BV>(512);
}
