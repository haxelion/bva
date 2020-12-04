use std::io::Cursor;
use std::iter::repeat;

use rand::{random, thread_rng, RngCore};
use rand::seq::SliceRandom;

use crate::{Bit, BitVector, Endianness};
use crate::dynamic::BVN;

const MAX_TESTED_SIZE: usize = 256;


fn random_bvn(length: usize) -> BVN {
    let byte_length = (length + 7) / 8;
    let mut bytes: Vec<u8> = repeat(0u8).take(byte_length).collect();
    thread_rng().fill_bytes(&mut bytes[..]);
    let mut bvn = BVN::from_bytes(&bytes, Endianness::LE);
    bvn.resize(length, Bit::Zero);
    return bvn;
}

#[test]
fn binary() {
    
    for length in 1..=MAX_TESTED_SIZE {
        let bv = random_bvn(length);
        let s1 = format!("{:b}", bv);
        let bv1 = BVN::from_binary(s1).unwrap();
        assert_eq!(bv, bv1);
    }
}

#[test]
fn hex() {
    for length in (4..=MAX_TESTED_SIZE).step_by(4) {
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

    for length in 1..=MAX_TESTED_SIZE {
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

    for length in 1..=MAX_TESTED_SIZE {
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

#[test]
fn resize_slice() {
    let mut bv = BVN::zeros(0);
    let mut length = 1;
    while bv.len() + length <= MAX_TESTED_SIZE {
        let bit = match length % 2 {
            0 => Bit::Zero,
            1 => Bit::One,
            _ => unreachable!()
        };
        bv.resize(bv.len() + length, bit);
        match bit {
            Bit::Zero => assert_eq!(BVN::zeros(length), bv.copy_slice((bv.len() - length)..bv.len())),
            Bit::One => assert_eq!(BVN::ones(length), bv.copy_slice((bv.len() - length)..bv.len())),
        }
        length += 1;
    }
}

#[test]
fn push_pop() {
    let mut bv = BVN::zeros(0);
    let mut bits = Vec::<Bit>::with_capacity(MAX_TESTED_SIZE); 

    for i in 0..MAX_TESTED_SIZE {
        let b = Bit::from(random::<bool>());
        bv.push(b);
        bits.push(b);
        assert_eq!(b, bv.get(i));
        assert_eq!(i + 1, bv.len());
    }

    for i in (0..MAX_TESTED_SIZE).rev() {
        let b = bits.pop().unwrap();
        assert_eq!(b, bv.get(i));
        assert_eq!(b, bv.pop().unwrap());
    }
}

#[test]
fn shift_in() {
    for length in 1..=MAX_TESTED_SIZE {
        let mut bv = BVN::zeros(length);
        // SHL
        for i in 0..length {
            assert_eq!(Bit::Zero, bv.shl_in(Bit::from((i + 1) % 2)));
            for j in 0..=i {
                assert_eq!(Bit::from((j + i + 1) % 2), bv.get(j));
            }
        }
        for i in 0..length {
            assert_eq!(Bit::from((i + 1) % 2), bv.shl_in(Bit::Zero));
            for j in 0..=i {
                assert_eq!(Bit::Zero, bv.get(j));
            }
        }
        // SHR
        for i in 0..length {
            assert_eq!(Bit::Zero, bv.shr_in(Bit::from((i + 1) % 2)));
            for j in 0..=i {
                assert_eq!(Bit::from((j + i + 1) % 2), bv.get(bv.len() - 1 - j));
            }
        }
        for i in 0..length {
            assert_eq!(Bit::from((i + 1) % 2), bv.shr_in(Bit::Zero));
            for j in 0..=i {
                assert_eq!(Bit::Zero, bv.get(bv.len() - 1 - j));
            }
        }
    }
}

#[test]
fn shift_rot() {
    for length in 1..=MAX_TESTED_SIZE {
        let mut bv = BVN::zeros(length);
        bv.set(0, Bit::One);
        let one = bv.clone();

        for r in 1..length {
            bv <<= r;
            assert_eq!(bv, &one << r);
            assert_eq!(bv, one.clone() << r);
            assert_eq!(Bit::One, bv.get(r));
            bv.rotl(length - r);
            assert_eq!(Bit::One, bv.get(0));
            bv.rotr(r);
            assert_eq!(Bit::One, bv.get(length - r));
            assert_eq!(&bv >> (length - r), one);
            assert_eq!(bv.clone() >> (length - r), one);
            bv >>= length - r;
            assert_eq!(Bit::One, bv.get(0));
        }
    }
}

#[test]
fn not() {
    for length in 1..=MAX_TESTED_SIZE {
        assert_eq!(BVN::ones(length), !BVN::zeros(length));
        assert_eq!(BVN::zeros(length), !BVN::ones(length));
        let bvo = BVN::ones(length);
        let bvz = BVN::zeros(length);
        assert_eq!(BVN::ones(length), !(&bvz));
        assert_eq!(BVN::zeros(length), !(&bvo));
    }
}