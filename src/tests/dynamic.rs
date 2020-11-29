use std::iter::repeat;

use rand::{random, thread_rng, RngCore};

use crate::{Bit, BitVector, Endianness};
use crate::dynamic::BVN;

// TODO: fix for arbitrary size
fn random_bvn(length: usize) -> BVN {
    let byte_length = (length + 7) / 8;
    let mut bytes: Vec<u8> = repeat(0u8).take(byte_length).collect();
    thread_rng().fill_bytes(&mut bytes[..]);
    return BVN::from_bytes(&bytes, Endianness::LE);
}

#[test]
fn binary() {
    // Implement arbitrary size
    for length in (8..=256).step_by(8) {
        let bv = random_bvn(length);
        let s1 = format!("{:b}", bv);
        let bv1 = BVN::from_binary(s1).unwrap();
        assert_eq!(bv, bv1);
    }
}

#[test]
fn hex() {
    // Implement arbitrary size
    for length in (8..=256).step_by(8) {
        let bv = random_bvn(length);

        let s1 = format!("{:x}", bv);
        let bv1 = BVN::from_hex(s1).unwrap();
        assert_eq!(bv, bv1);

        let s2 = format!("{:X}", bv);
        let bv2 = BVN::from_hex(s2).unwrap();
        assert_eq!(bv, bv2);

        let s3 = format!("{:#x}", bv);
        assert!(s3.starts_with("0x"));
        let bv3 = BVN::from_hex(&s3[2..]).unwrap();
        assert_eq!(bv, bv3);

        let s4 = format!("{:#X}", bv);
        assert!(s4.starts_with("0x"));
        let bv4 = BVN::from_hex(&s4[2..]).unwrap();
        assert_eq!(bv, bv4);
    }
}