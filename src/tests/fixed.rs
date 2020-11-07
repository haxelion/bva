use std::io::Cursor;
use std::iter::repeat;

use rand::random;

use crate::{Bit, BitVector, Endianness};
use crate::fixed::{BV8, BV16, BV32, BV64, BV128};

fn random_bv<BV: BitVector>(length: usize) -> BV {
    let mut bv = BV::zeros(length);
    for i in 0..length {
        bv.set(i, Bit::from(random::<bool>()));
    }
    return bv;
}

fn read_write_inner<BV: BitVector>(max_length: usize) {
    let num_bytes = max_length / 8;
    let mut buf: Cursor<Vec<u8>> = Cursor::new(repeat(0u8).take(num_bytes).collect());

    for length in 1..=max_length {
        let bv = random_bv::<BV>(length);

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
fn read_write() {
    read_write_inner::<BV8>(BV8::CAPACITY);
    read_write_inner::<BV16>(BV16::CAPACITY);
    read_write_inner::<BV32>(BV32::CAPACITY);
    read_write_inner::<BV64>(BV64::CAPACITY);
    read_write_inner::<BV128>(BV128::CAPACITY);
}

fn hex_inner<BV: BitVector>(max_length: usize) {
    for length in (4..=max_length).step_by(4) {
        let bv = random_bv::<BV>(length);

        let s1 = format!("{:x}", bv);
        let bv1 = BV::from_hex(s1).unwrap();
        assert_eq!(bv, bv1);

        let s2 = format!("{:X}", bv);
        let bv2 = BV::from_hex(s2).unwrap();
        assert_eq!(bv, bv2);
    }
}

#[test]
fn hex() {
    hex_inner::<BV8>(BV8::CAPACITY);
    hex_inner::<BV16>(BV16::CAPACITY);
    hex_inner::<BV32>(BV32::CAPACITY);
    hex_inner::<BV64>(BV64::CAPACITY);
    hex_inner::<BV128>(BV128::CAPACITY);
}


fn binary_inner<BV: BitVector>(max_length: usize) {
    for length in (4..=max_length).step_by(4) {
        let bv = random_bv::<BV>(length);

        let s1 = format!("{:b}", bv);
        let bv1 = BV::from_binary(s1).unwrap();
        assert_eq!(bv, bv1);
    }
}


#[test]
fn binary() {
    binary_inner::<BV8>(BV8::CAPACITY);
    binary_inner::<BV16>(BV16::CAPACITY);
    binary_inner::<BV32>(BV32::CAPACITY);
    binary_inner::<BV64>(BV64::CAPACITY);
    binary_inner::<BV128>(BV128::CAPACITY);
}