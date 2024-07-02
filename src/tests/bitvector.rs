use std::io::Cursor;
use std::iter::repeat;

use rand::seq::SliceRandom;
use rand::{thread_rng, Rng};

use crate::auto::BV;
use crate::bit::Bit;
use crate::dynamic::BVD;
use crate::fixed::BVF;
use crate::tests::{bvf_inner_unroll_cap, random_bv};
use crate::{BitVector, Endianness};

fn with_capacity_inner<B: BitVector>(max_capacity: usize) {
    for c in 0..max_capacity {
        let bv = B::with_capacity(c);
        assert!(bv.capacity() >= c);
        assert_eq!(bv.len(), 0);
    }
}

#[test]
fn with_capacity_bvf() {
    bvf_inner_unroll_cap!(with_capacity_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn with_capacity_bvd() {
    with_capacity_inner::<BVD>(256);
}

#[test]
fn with_capacity_bv() {
    with_capacity_inner::<BV>(256);
}

fn zeros_inner<B: BitVector>(max_capacity: usize) {
    for size in 0..max_capacity {
        let bv = B::zeros(size);
        assert_eq!(bv.len(), size);
        for i in 0..size {
            assert_eq!(bv.get(i), Bit::Zero);
        }
    }
}

#[test]
fn zeros_bvf() {
    bvf_inner_unroll_cap!(zeros_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn zeros_bvd() {
    zeros_inner::<BVD>(256);
}

#[test]
fn zeros_bv() {
    zeros_inner::<BV>(256);
}

fn ones_inner<B: BitVector>(max_capacity: usize) {
    for size in 0..max_capacity {
        let bv = B::ones(size);
        assert_eq!(bv.len(), size);
        for i in 0..size {
            assert_eq!(bv.get(i), Bit::One);
        }
    }
}

#[test]
fn ones_bvf() {
    bvf_inner_unroll_cap!(ones_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn ones_bvd() {
    ones_inner::<BVD>(256);
}

#[test]
fn ones_bv() {
    ones_inner::<BV>(256);
}

fn from_to_bytes_inner<B: BitVector>(max_capacity: usize) {
    for length in (8..=max_capacity).step_by(8) {
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
fn from_to_bytes_bvf() {
    bvf_inner_unroll_cap!(from_to_bytes_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_to_bytes_bvd() {
    from_to_bytes_inner::<BVD>(256);
}

#[test]
fn from_to_bytes_bv() {
    from_to_bytes_inner::<BV>(256);
}

fn read_write_inner<B: BitVector>(max_capacity: usize) {
    let num_bytes = max_capacity / 8;
    let mut buf: Cursor<Vec<u8>> = Cursor::new(repeat(0u8).take(num_bytes).collect());

    for length in (1..=max_capacity).rev() {
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
fn read_write_inner_bvf() {
    bvf_inner_unroll_cap!(read_write_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn read_write_inner_bvd() {
    read_write_inner::<BVD>(256);
}

#[test]
fn read_write_inner_bv() {
    read_write_inner::<BV>(256);
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
fn get_set_bvf() {
    bvf_inner_unroll_cap!(get_set_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn get_set_bvd() {
    get_set_inner::<BVD>(256);
}

#[test]
fn get_set_bv() {
    get_set_inner::<BV>(256);
}

fn copy_range_inner<B: BitVector>(max_capacity: usize) {
    let mut rng = thread_rng();
    for capacity in 0..max_capacity {
        let mut bv = B::zeros(0);
        let mut bits = Vec::new();

        for _ in 0..capacity {
            let b = Bit::from(rng.gen::<bool>());
            bv.push(b);
            bits.push(b);
        }

        for start in 0..capacity {
            for end in start..capacity {
                let slice = bv.copy_range(start..end);
                for (b1, &b2) in slice.iter().zip(bits[start..end].iter()) {
                    assert_eq!(b1, b2);
                }
            }
        }
    }
}

#[test]
fn copy_slice_bvf() {
    bvf_inner_unroll_cap!(copy_range_inner, {u8, u16, u32, u64}, {1, 2, 3, 4});
    bvf_inner_unroll_cap!(copy_range_inner, {u128}, {1, 2});
}

#[test]
fn copy_slice_bvd() {
    copy_range_inner::<BVD>(256);
}

#[test]
fn copy_slice_bv() {
    copy_range_inner::<BV>(256);
}

fn push_pop_inner<B: BitVector>(max_capacity: usize) {
    let mut rng = thread_rng();
    for capacity in 0..max_capacity {
        let mut bv = B::zeros(0);
        let mut bits = Vec::new();

        for i in 0..capacity {
            let b = Bit::from(rng.gen::<bool>());
            bv.push(b);
            bits.push(b);
            assert_eq!(b, bv.get(i));
            assert_eq!(i + 1, bv.len());
        }

        for i in (0..capacity).rev() {
            assert_eq!(
                bits[i],
                bv.pop().expect("BitVector should still contains bits")
            );
            assert_eq!(i, bv.len());
        }
    }
}

#[test]
fn push_pop_bvf() {
    bvf_inner_unroll_cap!(push_pop_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn push_pop_bvd() {
    push_pop_inner::<BVD>(256);
}

#[test]
fn push_pop_bv() {
    push_pop_inner::<BV>(256);
}

fn resize_inner<B: BitVector>(max_capacity: usize) {
    let mut bv = B::zeros(0);
    let mut length = 1;

    while bv.len() + length <= max_capacity {
        let bit = Bit::from(length % 2);

        bv.resize(bv.len() + length, bit);
        for i in 0..length {
            assert_eq!(bit, bv.get(bv.len() - length + i));
        }

        length += 1;
    }
}

#[test]
fn resize_bvf() {
    bvf_inner_unroll_cap!(resize_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn resize_bvd() {
    resize_inner::<BVD>(256);
}

#[test]
fn resize_bv() {
    resize_inner::<BV>(256);
}

fn shl_inner<B: BitVector>(max_capacity: usize) {
    let mut rng = thread_rng();
    for capacity in 0..max_capacity {
        let mut bv = random_bv::<B>(capacity);
        let mut bits: Vec<Bit> = bv.iter().collect();

        for _ in 0..capacity {
            let b = Bit::from(rng.gen::<bool>());
            let out = bv.shl_in(b);
            bits.insert(0, b);
            assert_eq!(out, bits.pop().unwrap());
            for (b1, &b2) in bv.iter().zip(bits.iter()) {
                assert_eq!(b1, b2);
            }
        }
    }
}

#[test]
fn shl_bvf() {
    bvf_inner_unroll_cap!(shl_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn shl_bvd() {
    shl_inner::<BVD>(256);
}

#[test]
fn shl_bv() {
    shl_inner::<BV>(256);
}

fn shr_inner<B: BitVector>(max_capacity: usize) {
    let mut rng = thread_rng();
    for capacity in 0..max_capacity {
        let mut bv = random_bv::<B>(capacity);
        let mut bits: Vec<Bit> = bv.iter().collect();

        for _ in 0..capacity {
            let b = Bit::from(rng.gen::<bool>());
            let out = bv.shr_in(b);
            bits.push(b);
            assert_eq!(out, bits.remove(0));
            for (b1, &b2) in bv.iter().zip(bits.iter()) {
                assert_eq!(b1, b2);
            }
        }
    }
}

#[test]
fn shr_bvf() {
    bvf_inner_unroll_cap!(shr_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn shr_bvd() {
    shr_inner::<BVD>(256);
}

#[test]
fn shr_bv() {
    shr_inner::<BV>(256);
}

fn rotl_inner<B: BitVector>(max_capacity: usize) {
    for capacity in 0..max_capacity {
        let bv = random_bv::<B>(capacity);

        for rotation in 0..capacity {
            let mut rotated = bv.clone();
            rotated.rotl(rotation);
            for i in 0..capacity {
                assert_eq!(bv.get(i), rotated.get((i + rotation) % capacity));
            }
        }
    }
}

#[test]
fn rotl_bvf() {
    bvf_inner_unroll_cap!(rotl_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn rotl_bvd() {
    rotl_inner::<BVD>(256);
}

#[test]
fn rotl_bv() {
    rotl_inner::<BV>(256);
}

fn rotr_inner<B: BitVector>(max_capacity: usize) {
    for capacity in 0..max_capacity {
        let bv = random_bv::<B>(capacity);

        for rotation in 0..capacity {
            let mut rotated = bv.clone();
            rotated.rotr(rotation);
            for i in 0..capacity {
                assert_eq!(bv.get((i + rotation) % capacity), rotated.get(i));
            }
        }
    }
}

#[test]
fn rotr_bvf() {
    bvf_inner_unroll_cap!(rotr_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn rotr_bvd() {
    rotr_inner::<BVD>(256);
}

#[test]
fn rotr_bv() {
    rotr_inner::<BV>(256);
}

fn is_empty_inner<B: BitVector>() {
    let bv = B::zeros(0);
    assert!(bv.is_empty());
    let bv = B::zeros(1);
    assert!(!bv.is_empty());
}

#[test]
fn is_empty_bvf() {
    is_empty_inner::<BVF<u8, 1>>();
    is_empty_inner::<BVF<u16, 1>>();
    is_empty_inner::<BVF<u32, 1>>();
    is_empty_inner::<BVF<u64, 1>>();
    is_empty_inner::<BVF<u128, 1>>();
}

#[test]
fn is_empty_bvd() {
    is_empty_inner::<BVD>();
}

#[test]
fn is_empty_bv() {
    is_empty_inner::<BV>();
}
