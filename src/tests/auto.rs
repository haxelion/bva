use std::convert::{TryFrom, TryInto};
use std::io::Cursor;
use std::iter::repeat;
use std::mem::size_of;
use std::num::Wrapping;

use rand::seq::SliceRandom;
use rand::{random, thread_rng, RngCore};

use crate::auto::BV;
use crate::dynamic::BVN;
use crate::fixed::{BV128, BV16, BV32, BV64, BV8};
use crate::{Bit, BitVector, Endianness};

const MAX_TESTED_SIZE: usize = 256;

fn random_bvn(length: usize) -> BVN {
    let byte_length = (length + 7) / 8;
    let mut bytes: Vec<u8> = repeat(0u8).take(byte_length).collect();
    thread_rng().fill_bytes(&mut bytes[..]);
    let mut bvn = BVN::from_bytes(&bytes, Endianness::LE).unwrap();
    bvn.resize(length, Bit::Zero);
    return bvn;
}

fn random_bv(length: usize) -> BV {
    let byte_length = (length + 7) / 8;
    let mut bytes: Vec<u8> = repeat(0u8).take(byte_length).collect();
    thread_rng().fill_bytes(&mut bytes[..]);
    let mut bv = BV::from_bytes(&bytes, Endianness::LE).unwrap();
    bv.resize(length, Bit::Zero);
    return bv;
}

#[test]
fn binary() {
    for length in 1..=MAX_TESTED_SIZE {
        let bv = random_bv(length);
        let s1 = format!("{:b}", bv);
        let bv1 = BV::from_binary(s1).unwrap();
        assert_eq!(bv, bv1);
    }
}

#[test]
fn hex() {
    for length in (4..=MAX_TESTED_SIZE).step_by(4) {
        let bv = random_bv(length);

        let s1 = format!("{:x}", bv);
        let bv1 = BV::from_hex(s1).unwrap();
        assert_eq!(bv, bv1);

        let s2 = format!("{:X}", bv);
        let bv2 = BV::from_hex(s2).unwrap();
        assert_eq!(bv, bv2);

        let s3 = format!("{:#x}", bv);
        assert!(s3.starts_with("0x"));
        let bv3 = BV::from_hex(&s3[2..]).unwrap();
        assert_eq!(bv, bv3);

        let s4 = format!("{:#X}", bv);
        assert!(s4.starts_with("0x"));
        let bv4 = BV::from_hex(&s4[2..]).unwrap();
        assert_eq!(bv, bv4);
    }
}

#[test]
fn from_to_bytes() {
    for length in (8..=MAX_TESTED_SIZE).step_by(8) {
        let bv = random_bv(length);

        let buf1 = bv.to_vec(Endianness::LE);
        let bv1 = BV::from_bytes(&buf1, Endianness::LE).unwrap();
        assert_eq!(bv, bv1);

        let buf2 = bv.to_vec(Endianness::BE);
        let bv2 = BV::from_bytes(&buf2, Endianness::BE).unwrap();
        assert_eq!(bv, bv2);
    }
}

#[test]
fn read_write() {
    let mut buf: Cursor<Vec<u8>> = Cursor::new(repeat(0u8).take(MAX_TESTED_SIZE).collect());

    for length in 1..=MAX_TESTED_SIZE {
        let bv = random_bv(length);

        buf.set_position(0);
        bv.write(&mut buf, Endianness::LE).unwrap();
        buf.set_position(0);
        let bv1 = BV::read(&mut buf, length, Endianness::LE).unwrap();
        assert_eq!(bv, bv1);

        buf.set_position(0);
        bv.write(&mut buf, Endianness::BE).unwrap();
        buf.set_position(0);
        let bv2 = BV::read(&mut buf, length, Endianness::BE).unwrap();
        assert_eq!(bv, bv2);
    }
}

#[test]
fn capacity() {
    for length in 1..=MAX_TESTED_SIZE {
        let bv1 = random_bv(length);
        let mut bv2 = bv1.clone();
        bv2.reserve(length);
        assert_eq!(bv1, bv2);
        bv2.shrink_to_fit();
        assert_eq!(bv1, bv2);
    }
}

#[test]
fn ord() {
    for length in 1..=MAX_TESTED_SIZE {
        assert!(BV::ones(length) > BV::zeros(length));
        let bv1 = random_bv(length);
        let bv2 = random_bv(length);
        if BV::ones(length) - &bv1 >= bv2 {
            assert!(bv1 <= &bv1 + &bv2);
        } else {
            assert!(bv1 > &bv1 + &bv2);
        }
    }
}

#[test]
fn get_set() {
    let mut rng = thread_rng();

    for length in 1..=MAX_TESTED_SIZE {
        let mut bv = BV::zeros(length);
        let mut indexes: Vec<usize> = (0..length).collect();

        indexes.shuffle(&mut rng);
        for &idx in &indexes {
            assert_eq!(Bit::Zero, bv.get(idx));
            bv.set(idx, Bit::One);
            assert_eq!(Bit::One, bv.get(idx));
        }
        assert_eq!(BV::ones(length), bv);

        indexes.shuffle(&mut rng);
        for &idx in &indexes {
            assert_eq!(Bit::One, bv.get(idx));
            bv.set(idx, Bit::Zero);
            assert_eq!(Bit::Zero, bv.get(idx));
        }
        assert_eq!(BV::zeros(length), bv);
    }
}

#[test]
fn resize_slice() {
    let mut bv = BV::zeros(0);
    let mut length = 1;
    while bv.len() + length <= MAX_TESTED_SIZE {
        let bit = match length % 2 {
            0 => Bit::Zero,
            1 => Bit::One,
            _ => unreachable!(),
        };
        bv.resize(bv.len() + length, bit);
        match bit {
            Bit::Zero => assert_eq!(
                BV::zeros(length),
                bv.copy_slice((bv.len() - length)..bv.len())
            ),
            Bit::One => assert_eq!(
                BV::ones(length),
                bv.copy_slice((bv.len() - length)..bv.len())
            ),
        }
        length += 1;
    }
}

#[test]
fn push_pop() {
    let mut bv = BV::zeros(0);
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
        let mut bv = BV::zeros(length);
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
        let mut bv = BV::zeros(length);
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
        assert_eq!(BV::ones(length), !BV::zeros(length));
        assert_eq!(BV::zeros(length), !BV::ones(length));
        let bvo = BV::ones(length);
        let bvz = BV::zeros(length);
        assert_eq!(BV::ones(length), !(&bvz));
        assert_eq!(BV::zeros(length), !(&bvo));
    }
}

#[test]
fn from_try_from() {
    let v: u8 = random();
    assert_eq!(v, BV::from(v).try_into().unwrap());
    assert_eq!(
        BV8::try_from(v).unwrap(),
        BV8::try_from(BV::from(BV8::try_from(v).unwrap())).unwrap()
    );
    let v: u16 = random();
    assert_eq!(v, BV::from(v).try_into().unwrap());
    assert_eq!(
        BV16::try_from(v).unwrap(),
        BV16::try_from(BV::from(BV16::try_from(v).unwrap())).unwrap()
    );
    let v: u32 = random();
    assert_eq!(v, BV::from(v).try_into().unwrap());
    assert_eq!(
        BV32::try_from(v).unwrap(),
        BV32::try_from(BV::from(BV32::try_from(v).unwrap())).unwrap()
    );
    let v: u64 = random();
    assert_eq!(v, BV::from(v).try_into().unwrap());
    assert_eq!(
        BV64::try_from(v).unwrap(),
        BV64::try_from(BV::from(BV64::try_from(v).unwrap())).unwrap()
    );
    let v: u128 = random();
    assert_eq!(v, BV::from(v).try_into().unwrap());
    assert_eq!(
        BV128::try_from(v).unwrap(),
        BV128::try_from(BV::from(BV128::try_from(v).unwrap())).unwrap()
    );
    for l in 128..=MAX_TESTED_SIZE {
        let v: BVN = random_bvn(l);
        assert_eq!(v, BVN::from(BV::from(&v)));
    }
}

#[test]
fn op() {
    for i in 1..=MAX_TESTED_SIZE {
        let a = random_bvn(i);
        let mut b = random_bvn(i);
        let bva = BV::from(&a);
        let mut bvb = BV::from(&b);

        // Test non assign variant first
        assert_eq!(!&a, BVN::from(!&bva));
        assert_eq!(&a & &b, BVN::from(&bva & &bvb));
        assert_eq!(&a | &b, BVN::from(&bva | &bvb));
        assert_eq!(&a ^ &b, BVN::from(&bva ^ &bvb));
        assert_eq!(&a + &b, BVN::from(&bva + &bvb));
        assert_eq!(&a - &b, BVN::from(&bva - &bvb));
        // BitAndAssign
        b &= &a;
        bvb &= &bva;
        assert_eq!(b, BVN::from(&bvb));
        // AddAssign
        b += &a;
        bvb += &bva;
        assert_eq!(b, BVN::from(&bvb));
        // BitOrAssign
        b |= &a;
        bvb |= &bva;
        assert_eq!(b, BVN::from(&bvb));
        // SubAssign
        b -= &a;
        bvb -= &bva;
        assert_eq!(b, BVN::from(&bvb));
        // BitXorAssign
        b ^= &a;
        bvb ^= &bva;
        assert_eq!(b, BVN::from(&bvb));
    }
}

macro_rules! decl_op_implicit_cast_inner {
    ($name:ident, $bvb:ty, $stb:ty) => {
        fn $name() {
            for i in 1..=(size_of::<u128>() * 8) {
                let mask = Wrapping(<u128>::MAX) >> (size_of::<u128>() * 8 - i);
                let mut a = Wrapping(random::<u128>()) & mask;
                let b = Wrapping(random::<$stb>() as u128) & mask;
                let mut bva = BV::from(a.0).copy_slice(0..i);
                let bvb = <$bvb>::try_from(b.0 as $stb)
                    .unwrap()
                    .copy_slice(0..(i.min(size_of::<$stb>() * 8)));

                // Test non assign variant first
                assert_eq!(((!a) & mask).0, u128::try_from(!&bva).unwrap());
                assert_eq!(((a & b) & mask).0, u128::try_from(&bva & &bvb).unwrap());
                assert_eq!(((a | b) & mask).0, u128::try_from(&bva | &bvb).unwrap());
                assert_eq!(((a ^ b) & mask).0, u128::try_from(&bva ^ &bvb).unwrap());
                assert_eq!(((a + b) & mask).0, u128::try_from(&bva + &bvb).unwrap());
                assert_eq!(((a - b) & mask).0, u128::try_from(&bva - &bvb).unwrap());
                // BitAndAssign
                a &= b;
                bva &= &bvb;
                assert_eq!(a.0, u128::try_from(&bva).unwrap());
                // AddAssign
                a += b;
                a &= mask;
                bva += &bvb;
                assert_eq!(a.0, u128::try_from(&bva).unwrap());
                // BitOrAssign
                a |= b;
                bva |= &bvb;
                assert_eq!(a.0, u128::try_from(&bva).unwrap());
                // SubAssign
                a -= b;
                a &= mask;
                bva -= &bvb;
                assert_eq!(a.0, u128::try_from(&bva).unwrap());
                // BitXorAssign
                a ^= b;
                bva ^= &bvb;
                assert_eq!(a.0, u128::try_from(&bva).unwrap());
            }
        }
    };
}

decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv8, BV8, u8);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv16, BV16, u16);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv32, BV32, u32);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv64, BV64, u64);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv128, BV128, u128);

#[test]
fn op_implicit_cast() {
    op_implicit_cast_inner_bv8();
    op_implicit_cast_inner_bv16();
    op_implicit_cast_inner_bv32();
    op_implicit_cast_inner_bv64();
    op_implicit_cast_inner_bv128();
}
