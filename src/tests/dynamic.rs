use std::io::Cursor;
use std::iter::repeat;

use rand::{random, thread_rng, RngCore};
use rand::seq::SliceRandom;

use crate::{Bit, BitVector, Endianness};
use crate::dynamic::BVN;

const MAX_TESTED_SIZE: usize = 1024;

// TODO: fix for arbitrary size
fn random_bvn(length: usize) -> BVN {
    let byte_length = (length + 7) / 8;
    let mut bytes: Vec<u8> = repeat(0u8).take(byte_length).collect();
    thread_rng().fill_bytes(&mut bytes[..]);
    return BVN::from_bytes(&bytes, Endianness::LE);
}

#[test]
fn binary() {
    // TODO: Implement arbitrary size
    for length in (8..=MAX_TESTED_SIZE).step_by(8) {
        let bv = random_bvn(length);
        let s1 = format!("{:b}", bv);
        let bv1 = BVN::from_binary(s1).unwrap();
        assert_eq!(bv, bv1);
    }
}

#[test]
fn hex() {
    // TODO: Implement arbitrary size
    for length in (8..=MAX_TESTED_SIZE).step_by(8) {
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

#[test]
fn from_to_bytes() {
    for length in (8..=MAX_TESTED_SIZE).step_by(8) {
        let bv = random_bvn(length);

        let buf1 = bv.to_vec(Endianness::LE);
        let bv1 = BVN::from_bytes(&buf1, Endianness::LE);
        assert_eq!(bv, bv1);

        let buf2 = bv.to_vec(Endianness::BE);
        let bv2 = BVN::from_bytes(&buf2, Endianness::BE);
        assert_eq!(bv, bv2);
    }
}

#[test]
fn read_write() {
    let mut buf: Cursor<Vec<u8>> = Cursor::new(repeat(0u8).take(MAX_TESTED_SIZE).collect());

    // TODO: Implement arbitrary size
    for length in (8..=MAX_TESTED_SIZE).step_by(8) {
        let bv = random_bvn(length);

        buf.set_position(0);
        bv.write(&mut buf, Endianness::LE).unwrap();
        buf.set_position(0);
        let bv1 = BVN::read(&mut buf, length, Endianness::LE).unwrap();
        assert_eq!(bv, bv1);

        buf.set_position(0);
        bv.write(&mut buf, Endianness::BE).unwrap();
        buf.set_position(0);
        let bv2 = BVN::read(&mut buf, length, Endianness::BE).unwrap();
        assert_eq!(bv, bv2);
    }
}

#[test]
fn get_set() {
    let mut rng = thread_rng();

    for length in 1..MAX_TESTED_SIZE {
        let mut bv = BVN::zeros(length);
        let mut indexes: Vec<usize> = (0..length).collect();

        indexes.shuffle(&mut rng);
        for &idx in &indexes {
            assert_eq!(Bit::Zero, bv.get(idx));
            bv.set(idx, Bit::One);
            assert_eq!(Bit::One, bv.get(idx));
        }
        assert_eq!(BVN::ones(length), bv);

        indexes.shuffle(&mut rng);
        for &idx in &indexes {
            assert_eq!(Bit::One, bv.get(idx));
            bv.set(idx, Bit::Zero);
            assert_eq!(Bit::Zero, bv.get(idx));
        }
        assert_eq!(BVN::zeros(length), bv);
    }
}