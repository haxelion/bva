use std::io::Cursor;
use std::iter::repeat;
use std::mem::size_of;
use std::num::Wrapping;

use rand::{random, thread_rng};
use rand::seq::SliceRandom;

use crate::{Bit, BitVector, Endianness};
use crate::fixed::{BV8, BV16, BV32, BV64, BV128};

fn random_bv<BV: BitVector>(length: usize) -> BV {
    let mut bv = BV::zeros(length);
    for i in 0..length {
        bv.set(i, Bit::from(random::<bool>()));
    }
    return bv;
}

fn get_set_inner<BV: BitVector>(capacity: usize) {
    let mut rng = thread_rng();

    for length in 1..capacity {
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
fn get_set() {
    get_set_inner::<BV8>(BV8::CAPACITY);
    get_set_inner::<BV16>(BV16::CAPACITY);
    get_set_inner::<BV32>(BV32::CAPACITY);
    get_set_inner::<BV64>(BV64::CAPACITY);
    get_set_inner::<BV128>(BV128::CAPACITY);
}

macro_rules! decl_push_pop_inner {($name:ident, $bv:ty, $st:ty) => {
    fn $name(capacity: usize) {
        let mut bv = <$bv>::zeros(0);
        let mut int: $st = 0;

        for i in 0..capacity {
            let b = Bit::from(random::<bool>());
            int |= <$st>::from(b) << i;
            bv.push(b);
            assert_eq!(b, bv.get(i));
            assert_eq!(int, <$st>::from(bv));
        }

        for i in (0..capacity).rev() {
            let b = Bit::from((int >> i) & 1);
            assert_eq!(b, bv.pop().unwrap());
        }
    }
}}

decl_push_pop_inner!(push_pop_inner_bv8, BV8, u8);
decl_push_pop_inner!(push_pop_inner_bv16, BV16, u16);
decl_push_pop_inner!(push_pop_inner_bv32, BV32, u32);
decl_push_pop_inner!(push_pop_inner_bv64, BV64, u64);
decl_push_pop_inner!(push_pop_inner_bv128, BV128, u128);

#[test]
fn push_pop() {
    push_pop_inner_bv8(BV8::CAPACITY);
    push_pop_inner_bv16(BV16::CAPACITY);
    push_pop_inner_bv32(BV32::CAPACITY);
    push_pop_inner_bv64(BV64::CAPACITY);
    push_pop_inner_bv128(BV128::CAPACITY);
}

macro_rules! decl_shift_rot_inner {($name:ident, $bv:ty, $st:ty) => {
    fn $name(capacity: usize) {
        for length in 1..capacity {
            let mut bv = <$bv>::zeros(length);
            bv.set(0, Bit::One);
            let one = bv.clone();

            for r in 1..length {
                bv <<= r;
                assert_eq!(bv, one << r);
                assert_eq!(1 << r, <$st>::from(bv));
                bv.rotl(length - r);
                assert_eq!(1, <$st>::from(bv));
                bv.rotr(r);
                assert_eq!(1 << (length - r), <$st>::from(bv));
                assert_eq!(bv >> (length - r), one);
                bv >>= length - r;
                assert_eq!(1, <$st>::from(bv));
            }
        }
    }
}}

decl_shift_rot_inner!(shift_rot_inner_bv8, BV8, u8);
decl_shift_rot_inner!(shift_rot_inner_bv16, BV16, u16);
decl_shift_rot_inner!(shift_rot_inner_bv32, BV32, u32);
decl_shift_rot_inner!(shift_rot_inner_bv64, BV64, u64);
decl_shift_rot_inner!(shift_rot_inner_bv128, BV128, u128);

#[test]
fn shift_rot() {
    shift_rot_inner_bv8(BV8::CAPACITY);
    shift_rot_inner_bv16(BV16::CAPACITY);
    shift_rot_inner_bv32(BV32::CAPACITY);
    shift_rot_inner_bv64(BV64::CAPACITY);
    shift_rot_inner_bv128(BV128::CAPACITY);
}

macro_rules! decl_resize_slice_inner {($name:ident, $bv:ty, $st:ty) => {
    fn $name(capacity: usize) {
        let mut bv = <$bv>::zeros(0);
        let mut length = 1;
        while bv.len() + length <= capacity {
            let bit = match length % 2 {
                0 => Bit::Zero,
                1 => Bit::One,
                _ => unreachable!()
            };
            bv.resize(bv.len() + length, bit);
            match bit {
                Bit::Zero => assert_eq!(<$bv>::zeros(length), bv.copy_slice((bv.len() - length)..bv.len())),
                Bit::One => assert_eq!(<$bv>::ones(length), bv.copy_slice((bv.len() - length)..bv.len())),
            }
            length += 1;
        }
    }
}}

decl_resize_slice_inner!(resize_slice_inner_bv8, BV8, u8);
decl_resize_slice_inner!(resize_slice_inner_bv16, BV16, u16);
decl_resize_slice_inner!(resize_slice_inner_bv32, BV32, u32);
decl_resize_slice_inner!(resize_slice_inner_bv64, BV64, u64);
decl_resize_slice_inner!(resize_slice_inner_bv128, BV128, u128);

#[test]
fn resize_slice() {
    resize_slice_inner_bv8(BV8::CAPACITY);
    resize_slice_inner_bv16(BV16::CAPACITY);
    resize_slice_inner_bv32(BV32::CAPACITY);
    resize_slice_inner_bv64(BV64::CAPACITY);
    resize_slice_inner_bv128(BV128::CAPACITY);
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

macro_rules! decl_op_inner {($name:ident, $bv:ty, $st:ty) => {
    fn $name() {
        for i in 1..=(size_of::<$st>() * 8) {
            let mask = Wrapping(<$st>::MAX) >> (size_of::<$st>() * 8 - i);
            let a = Wrapping(random::<$st>()) & mask;
            let mut b = Wrapping(random::<$st>()) & mask;
            let bva = <$bv>::from(a.0).copy_slice(0..i);
            let mut bvb = <$bv>::from(b.0).copy_slice(0..i);

            // Test non assign variant first
            assert_eq!(((!a) & mask).0, <$st>::from(!bva));
            assert_eq!(((a & b) & mask).0, <$st>::from(bva & bvb));
            assert_eq!(((a | b) & mask).0, <$st>::from(bva | bvb));
            assert_eq!(((a ^ b) & mask).0, <$st>::from(bva ^ bvb));
            assert_eq!(((a + b) & mask).0, <$st>::from(bva + bvb));
            assert_eq!(((a - b) & mask).0, <$st>::from(bva - bvb));
            // BitAndAssign
            b &= a;
            bvb &= bva;
            assert_eq!(b.0, <$st>::from(bvb));
            // AddAssign
            b += a;
            b &= mask;
            bvb += bva;
            assert_eq!(b.0, <$st>::from(bvb));
            // BitOrAssign
            b |= a;
            bvb |= bva;
            assert_eq!(b.0, <$st>::from(bvb));
            // SubAssign
            b -= a;
            b &= mask;
            bvb -= bva;
            assert_eq!(b.0, <$st>::from(bvb));
            // BitXorAssign
            b ^= a;
            bvb ^= bva;
            assert_eq!(b.0, <$st>::from(bvb));
        }
    }
}}

decl_op_inner!(op_inner_bv8, BV8, u8);
decl_op_inner!(op_inner_bv16, BV16, u16);
decl_op_inner!(op_inner_bv32, BV32, u32);
decl_op_inner!(op_inner_bv64, BV64, u64);
decl_op_inner!(op_inner_bv128, BV128, u128);

#[test]
fn op() {
    op_inner_bv8();
    op_inner_bv16();
    op_inner_bv32();
    op_inner_bv64();
    op_inner_bv128();
}

macro_rules! decl_op_implicit_cast_inner {($name:ident, $bva:ty, $sta:ty, $bvb:ty, $stb:ty) => {
    fn $name() {
        for i in 1..=(size_of::<$sta>() * 8) {
            let mask = Wrapping(<$sta>::MAX) >> (size_of::<$sta>() * 8 - i);
            let mut a = Wrapping(random::<$sta>()) & mask;
            let b = Wrapping(random::<$stb>() as $sta) & mask;
            let mut bva = <$bva>::from(a.0).copy_slice(0..i);
            let bvb = <$bvb>::from(b.0 as $stb).copy_slice(0..(i.min(size_of::<$stb>() * 8)));

            // Test non assign variant first
            assert_eq!(((!a) & mask).0, <$sta>::from(!bva));
            assert_eq!(((a & b) & mask).0, <$sta>::from(bva & bvb));
            assert_eq!(((a | b) & mask).0, <$sta>::from(bva | bvb));
            assert_eq!(((a ^ b) & mask).0, <$sta>::from(bva ^ bvb));
            assert_eq!(((a + b) & mask).0, <$sta>::from(bva + bvb));
            assert_eq!(((a - b) & mask).0, <$sta>::from(bva - bvb));
            // BitAndAssign
            a &= b;
            bva &= bvb;
            assert_eq!(a.0, <$sta>::from(bva));
            // AddAssign
            a += b;
            a &= mask;
            bva += bvb;
            assert_eq!(a.0, <$sta>::from(bva));
            // BitOrAssign
            a |= b;
            bva |= bvb;
            assert_eq!(a.0, <$sta>::from(bva));
            // SubAssign
            a -= b;
            a &= mask;
            bva -= bvb;
            assert_eq!(a.0, <$sta>::from(bva));
            // BitXorAssign
            a ^= b;
            bva ^= bvb;
            assert_eq!(a.0, <$sta>::from(bva));
        }
    }
}}

decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv16_bv8, BV16, u16, BV8, u8);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv32_bv8, BV32, u32, BV8, u8);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv32_bv16, BV32, u32, BV16, u16);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv64_bv8, BV64, u64, BV8, u8);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv64_bv16, BV64, u64, BV16, u16);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv64_bv32, BV64, u64, BV32, u32);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv128_bv8, BV128, u128, BV8, u8);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv128_bv16, BV128, u128, BV16, u16);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv128_bv32, BV128, u128, BV32, u32);
decl_op_implicit_cast_inner!(op_implicit_cast_inner_bv128_bv64, BV128, u128, BV64, u64);

#[test]
fn op_implicit_cast() {
    op_implicit_cast_inner_bv16_bv8();
    op_implicit_cast_inner_bv32_bv8();
    op_implicit_cast_inner_bv32_bv16();
    op_implicit_cast_inner_bv64_bv8();
    op_implicit_cast_inner_bv64_bv16();
    op_implicit_cast_inner_bv64_bv32();
    op_implicit_cast_inner_bv128_bv8();
    op_implicit_cast_inner_bv128_bv16();
    op_implicit_cast_inner_bv128_bv32();
    op_implicit_cast_inner_bv128_bv64();
}