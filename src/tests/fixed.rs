use std::convert::TryFrom;
use std::io::Cursor;
use std::iter::repeat;
use std::mem::size_of;
use std::num::Wrapping;

use rand::seq::SliceRandom;
use rand::{random, thread_rng};

use crate::fixed::{BV128, BV16, BV192, BV256, BV32, BV320, BV384, BV448, BV512, BV64, BV8};
use crate::{Bit, BitVector, Endianness};

fn random_bv<B: BitVector>(length: usize) -> B {
    let mut bv = B::zeros(length);
    for i in 0..length {
        bv.set(i, Bit::from(random::<bool>()));
    }
    return bv;
}

fn get_set_inner<B: BitVector>(capacity: usize) {
    let mut rng = thread_rng();

    for length in 1..capacity {
        let mut bv = B::zeros(length);
        let mut indexes: Vec<usize> = (0..length).collect();

        indexes.shuffle(&mut rng);
        for &idx in &indexes {
            assert_eq!(Bit::Zero, bv.get(idx));
            bv.set(idx, Bit::One);
            assert_eq!(Bit::One, bv.get(idx));
        }
        assert_eq!(B::ones(length), bv);

        indexes.shuffle(&mut rng);
        for &idx in &indexes {
            assert_eq!(Bit::One, bv.get(idx));
            bv.set(idx, Bit::Zero);
            assert_eq!(Bit::Zero, bv.get(idx));
        }
        assert_eq!(B::zeros(length), bv);
    }
}

#[test]
fn get_set() {
    get_set_inner::<BV8>(BV8::capacity());
    get_set_inner::<BV16>(BV16::capacity());
    get_set_inner::<BV32>(BV32::capacity());
    get_set_inner::<BV64>(BV64::capacity());
    get_set_inner::<BV128>(BV128::capacity());
    get_set_inner::<BV192>(BV192::capacity());
    get_set_inner::<BV256>(BV256::capacity());
    get_set_inner::<BV320>(BV320::capacity());
    get_set_inner::<BV384>(BV384::capacity());
    get_set_inner::<BV448>(BV448::capacity());
    get_set_inner::<BV512>(BV512::capacity());
}

macro_rules! decl_push_pop_inner {
    ($name:ident, $bv:ty, $st:ty) => {
        fn $name(capacity: usize) {
            let mut bv = <$bv>::zeros(0);
            let mut int: $st = 0;

            for i in 0..capacity {
                let b = Bit::from(random::<bool>());
                int |= <$st>::try_from(b).unwrap() << i;
                bv.push(b);
                assert_eq!(b, bv.get(i));
                assert_eq!(int, <$st>::try_from(bv).unwrap());
            }

            for i in (0..capacity).rev() {
                let b = Bit::from((int >> i) & 1);
                assert_eq!(b, bv.pop().unwrap());
            }
        }
    };
}

decl_push_pop_inner!(push_pop_inner_bv8, BV8, u8);
decl_push_pop_inner!(push_pop_inner_bv16, BV16, u16);
decl_push_pop_inner!(push_pop_inner_bv32, BV32, u32);
decl_push_pop_inner!(push_pop_inner_bv64, BV64, u64);
decl_push_pop_inner!(push_pop_inner_bv128, BV128, u128);

#[test]
fn push_pop() {
    push_pop_inner_bv8(BV8::capacity());
    push_pop_inner_bv16(BV16::capacity());
    push_pop_inner_bv32(BV32::capacity());
    push_pop_inner_bv64(BV64::capacity());
    push_pop_inner_bv128(BV128::capacity());
}

macro_rules! decl_shift_rot_inner {
    ($name:ident, $bv:ty, $st:ty) => {
        fn $name(capacity: usize) {
            for length in 1..=capacity {
                let mut bv = <$bv>::zeros(length);
                bv.set(0, Bit::One);
                let one = bv.clone();

                for r in 1..length {
                    bv <<= r;
                    assert_eq!(bv, one << r);
                    assert_eq!(1 << r, <$st>::try_from(bv).unwrap());
                    bv.rotl(length - r);
                    assert_eq!(1, <$st>::try_from(bv).unwrap());
                    bv.rotr(r);
                    assert_eq!(1 << (length - r), <$st>::try_from(bv).unwrap());
                    assert_eq!(bv >> (length - r), one);
                    bv >>= length - r;
                    assert_eq!(1, <$st>::try_from(bv).unwrap());
                }
            }
        }
    };
}

decl_shift_rot_inner!(shift_rot_inner_bv8, BV8, u8);
decl_shift_rot_inner!(shift_rot_inner_bv16, BV16, u16);
decl_shift_rot_inner!(shift_rot_inner_bv32, BV32, u32);
decl_shift_rot_inner!(shift_rot_inner_bv64, BV64, u64);
decl_shift_rot_inner!(shift_rot_inner_bv128, BV128, u128);

#[test]
fn shift_rot() {
    shift_rot_inner_bv8(BV8::capacity());
    shift_rot_inner_bv16(BV16::capacity());
    shift_rot_inner_bv32(BV32::capacity());
    shift_rot_inner_bv64(BV64::capacity());
    shift_rot_inner_bv128(BV128::capacity());
}

macro_rules! decl_resize_slice_inner {
    ($name:ident, $bv:ty, $st:ty) => {
        fn $name(capacity: usize) {
            let mut bv = <$bv>::zeros(0);
            let mut length = 1;
            while bv.len() + length <= capacity {
                let bit = match length % 2 {
                    0 => Bit::Zero,
                    1 => Bit::One,
                    _ => unreachable!(),
                };
                bv.resize(bv.len() + length, bit);
                match bit {
                    Bit::Zero => assert_eq!(
                        <$bv>::zeros(length),
                        bv.copy_slice((bv.len() - length)..bv.len())
                    ),
                    Bit::One => assert_eq!(
                        <$bv>::ones(length),
                        bv.copy_slice((bv.len() - length)..bv.len())
                    ),
                }
                length += 1;
            }
        }
    };
}

decl_resize_slice_inner!(resize_slice_inner_bv8, BV8, u8);
decl_resize_slice_inner!(resize_slice_inner_bv16, BV16, u16);
decl_resize_slice_inner!(resize_slice_inner_bv32, BV32, u32);
decl_resize_slice_inner!(resize_slice_inner_bv64, BV64, u64);
decl_resize_slice_inner!(resize_slice_inner_bv128, BV128, u128);

#[test]
fn resize_slice() {
    resize_slice_inner_bv8(BV8::capacity());
    resize_slice_inner_bv16(BV16::capacity());
    resize_slice_inner_bv32(BV32::capacity());
    resize_slice_inner_bv64(BV64::capacity());
    resize_slice_inner_bv128(BV128::capacity());
}

fn from_to_bytes_inner<B: BitVector>(max_length: usize) {
    for length in (8..=max_length).step_by(8) {
        let bv = random_bv::<B>(length);

        let buf1 = bv.to_vec(Endianness::LE);
        let bv1 = B::from_bytes(&buf1, Endianness::LE).unwrap();
        assert_eq!(bv, bv1);

        let buf2 = bv.to_vec(Endianness::BE);
        let bv2 = B::from_bytes(&buf2, Endianness::BE).unwrap();
        assert_eq!(bv, bv2);
    }
}

#[test]
fn from_to_bytes() {
    from_to_bytes_inner::<BV8>(BV8::capacity());
    from_to_bytes_inner::<BV16>(BV16::capacity());
    from_to_bytes_inner::<BV32>(BV32::capacity());
    from_to_bytes_inner::<BV64>(BV64::capacity());
    from_to_bytes_inner::<BV128>(BV128::capacity());
    from_to_bytes_inner::<BV192>(BV192::capacity());
    from_to_bytes_inner::<BV256>(BV256::capacity());
    from_to_bytes_inner::<BV320>(BV320::capacity());
    from_to_bytes_inner::<BV384>(BV384::capacity());
    from_to_bytes_inner::<BV448>(BV448::capacity());
    from_to_bytes_inner::<BV512>(BV512::capacity());
}

fn read_write_inner<B: BitVector>(max_length: usize) {
    let num_bytes = max_length / 8;
    let mut buf: Cursor<Vec<u8>> = Cursor::new(repeat(0u8).take(num_bytes).collect());

    for length in (1..=max_length).rev() {
        let bv = random_bv::<B>(length);

        buf.set_position(0);
        bv.write(&mut buf, Endianness::LE).unwrap();
        buf.set_position(0);
        let bv1 = B::read(&mut buf, length, Endianness::LE).unwrap();
        assert_eq!(bv, bv1);

        buf.set_position(0);
        bv.write(&mut buf, Endianness::BE).unwrap();
        buf.set_position(0);
        let bv2 = B::read(&mut buf, length, Endianness::BE).unwrap();
        assert_eq!(bv, bv2);
    }
}

#[test]
fn read_write() {
    read_write_inner::<BV8>(BV8::capacity());
    read_write_inner::<BV16>(BV16::capacity());
    read_write_inner::<BV32>(BV32::capacity());
    read_write_inner::<BV64>(BV64::capacity());
    read_write_inner::<BV128>(BV128::capacity());
    read_write_inner::<BV192>(BV192::capacity());
    read_write_inner::<BV256>(BV256::capacity());
    read_write_inner::<BV320>(BV320::capacity());
    read_write_inner::<BV384>(BV384::capacity());
    read_write_inner::<BV448>(BV448::capacity());
    read_write_inner::<BV512>(BV512::capacity());
}

fn hex_inner<B: BitVector>(max_length: usize) {
    for length in (4..=max_length).step_by(4) {
        let bv = random_bv::<B>(length);

        let s1 = format!("{:x}", bv);
        let bv1 = B::from_hex(s1).unwrap();
        assert_eq!(bv, bv1);

        let s2 = format!("{:X}", bv);
        let bv2 = B::from_hex(s2).unwrap();
        assert_eq!(bv, bv2);

        let s3 = format!("{:#x}", bv);
        assert!(s3.starts_with("0x"));
        let bv3 = B::from_hex(&s3[2..]).unwrap();
        assert_eq!(bv, bv3);

        let s4 = format!("{:#X}", bv);
        assert!(s4.starts_with("0x"));
        let bv4 = B::from_hex(&s4[2..]).unwrap();
        assert_eq!(bv, bv4);
    }
}

#[test]
fn hex() {
    hex_inner::<BV8>(BV8::capacity());
    hex_inner::<BV16>(BV16::capacity());
    hex_inner::<BV32>(BV32::capacity());
    hex_inner::<BV64>(BV64::capacity());
    hex_inner::<BV128>(BV128::capacity());
    hex_inner::<BV192>(BV192::capacity());
    hex_inner::<BV256>(BV256::capacity());
    hex_inner::<BV320>(BV320::capacity());
    hex_inner::<BV384>(BV384::capacity());
    hex_inner::<BV448>(BV448::capacity());
    hex_inner::<BV512>(BV512::capacity());
}

fn binary_inner<B: BitVector>(max_length: usize) {
    for length in (4..=max_length).step_by(4) {
        let bv = random_bv::<B>(length);

        let s1 = format!("{:b}", bv);
        let bv1 = B::from_binary(s1).unwrap();
        assert_eq!(bv, bv1);
    }
}

#[test]
fn binary() {
    binary_inner::<BV8>(BV8::capacity());
    binary_inner::<BV16>(BV16::capacity());
    binary_inner::<BV32>(BV32::capacity());
    binary_inner::<BV64>(BV64::capacity());
    binary_inner::<BV128>(BV128::capacity());
    binary_inner::<BV192>(BV192::capacity());
    binary_inner::<BV256>(BV256::capacity());
    binary_inner::<BV320>(BV320::capacity());
    binary_inner::<BV384>(BV384::capacity());
    binary_inner::<BV448>(BV448::capacity());
    binary_inner::<BV512>(BV512::capacity());
}

macro_rules! decl_op_inner {
    ($name:ident, $bv:ty, $st:ty) => {
        fn $name() {
            for i in 1..=(size_of::<$st>() * 8) {
                let mask = Wrapping(<$st>::MAX) >> (size_of::<$st>() * 8 - i);
                let a = Wrapping(random::<$st>()) & mask;
                let mut b = Wrapping(random::<$st>()) & mask;
                let bva = <$bv>::try_from(a.0).unwrap().copy_slice(0..i);
                let mut bvb = <$bv>::try_from(b.0).unwrap().copy_slice(0..i);

                // Test non assign variant first
                assert_eq!(((!a) & mask).0, <$st>::try_from(!bva).unwrap());
                assert_eq!(((a & b) & mask).0, <$st>::try_from(bva & bvb).unwrap());
                assert_eq!(((a | b) & mask).0, <$st>::try_from(bva | bvb).unwrap());
                assert_eq!(((a ^ b) & mask).0, <$st>::try_from(bva ^ bvb).unwrap());
                assert_eq!(((a + b) & mask).0, <$st>::try_from(bva + bvb).unwrap());
                assert_eq!(((a - b) & mask).0, <$st>::try_from(bva - bvb).unwrap());
                // BitAndAssign
                b &= a;
                bvb &= bva;
                assert_eq!(b.0, <$st>::try_from(bvb).unwrap());
                // AddAssign
                b += a;
                b &= mask;
                bvb += bva;
                assert_eq!(b.0, <$st>::try_from(bvb).unwrap());
                // BitOrAssign
                b |= a;
                bvb |= bva;
                assert_eq!(b.0, <$st>::try_from(bvb).unwrap());
                // SubAssign
                b -= a;
                b &= mask;
                bvb -= bva;
                assert_eq!(b.0, <$st>::try_from(bvb).unwrap());
                // BitXorAssign
                b ^= a;
                bvb ^= bva;
                assert_eq!(b.0, <$st>::try_from(bvb).unwrap());
            }
        }
    };
}

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

macro_rules! decl_op_implicit_cast_inner {
    ($name:ident, $bva:ty, $sta:ty, $bvb:ty, $stb:ty) => {
        fn $name() {
            for i in 1..=(size_of::<$sta>() * 8) {
                let mask = Wrapping(<$sta>::MAX) >> (size_of::<$sta>() * 8 - i);
                let mut a = Wrapping(random::<$sta>()) & mask;
                let b = Wrapping(random::<$stb>() as $sta) & mask;
                let mut bva = <$bva>::try_from(a.0).unwrap().copy_slice(0..i);
                let bvb = <$bvb>::try_from(b.0 as $stb)
                    .unwrap()
                    .copy_slice(0..(i.min(size_of::<$stb>() * 8)));

                // sanity checks
                assert_eq!((a & mask).0, <$sta>::try_from(bva).unwrap());
                assert_eq!((b & mask).0, <$sta>::try_from(bvb).unwrap());

                // Test non assign variant first
                assert_eq!(((!a) & mask).0, <$sta>::try_from(!bva).unwrap());
                assert_eq!(((a & b) & mask).0, <$sta>::try_from(bva & bvb).unwrap());
                assert_eq!(((a | b) & mask).0, <$sta>::try_from(bva | bvb).unwrap());
                assert_eq!(((a ^ b) & mask).0, <$sta>::try_from(bva ^ bvb).unwrap());
                assert_eq!(((a + b) & mask).0, <$sta>::try_from(bva + bvb).unwrap());
                assert_eq!(((a - b) & mask).0, <$sta>::try_from(bva - bvb).unwrap());
                // BitAndAssign
                a &= b;
                bva &= bvb;
                //assert_eq!(a.0, <$sta>::try_from(bva).unwrap());
                // AddAssign
                a += b;
                a &= mask;
                bva += bvb;
                assert_eq!(a.0, <$sta>::try_from(bva).unwrap());
                // BitOrAssign
                a |= b;
                bva |= bvb;
                assert_eq!(a.0, <$sta>::try_from(bva).unwrap());
                // SubAssign
                a -= b;
                a &= mask;
                bva -= bvb;
                assert_eq!(a.0, <$sta>::try_from(bva).unwrap());
                // BitXorAssign
                a ^= b;
                bva ^= bvb;
                assert_eq!(a.0, <$sta>::try_from(bva).unwrap());
            }
        }
    };
}

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

fn shift_in_inner<B: BitVector>(capacity: usize) {
    for length in 1..=capacity {
        let mut bv = B::zeros(length);
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

// This test is slow because it's quadratic
#[test]
fn shift_in() {
    shift_in_inner::<BV8>(BV8::capacity());
    shift_in_inner::<BV16>(BV16::capacity());
    shift_in_inner::<BV32>(BV32::capacity());
    shift_in_inner::<BV64>(BV64::capacity());
    shift_in_inner::<BV128>(BV128::capacity());
    shift_in_inner::<BV192>(BV192::capacity());
    shift_in_inner::<BV256>(BV256::capacity());
    shift_in_inner::<BV320>(BV320::capacity());
    shift_in_inner::<BV384>(BV384::capacity());
    shift_in_inner::<BV448>(BV448::capacity());
    shift_in_inner::<BV512>(BV512::capacity());
}
