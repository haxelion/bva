use std::io::Cursor;
use std::iter::repeat;

use rand::seq::SliceRandom;
use rand::{thread_rng, Rng, RngCore};

use crate::auto::BV;
use crate::bit::Bit;
use crate::dynamic::BVD;
use crate::fixed::BVF;
use crate::tests::{bvf_inner_unroll_cap, random_bv};
use crate::{BitVector, ConvertionError, Endianness};

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

    let mut buffer: Vec<_> = repeat(0u8).take(64).collect();
    thread_rng().fill_bytes(&mut buffer);
    assert_eq!(
        BVF::<u8, 2>::from_bytes(&buffer, Endianness::BE),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        BVF::<u16, 2>::from_bytes(&buffer, Endianness::BE),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        BVF::<u32, 2>::from_bytes(&buffer, Endianness::BE),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        BVF::<u64, 2>::from_bytes(&buffer, Endianness::BE),
        Err(ConvertionError::NotEnoughCapacity)
    );
    assert_eq!(
        BVF::<u128, 2>::from_bytes(&buffer, Endianness::BE),
        Err(ConvertionError::NotEnoughCapacity)
    );
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

    let mut buffer: Vec<_> = repeat(0u8).take(64).collect();
    thread_rng().fill_bytes(&mut buffer);
    assert!(BVF::<u8, 2>::read(&mut Cursor::new(&buffer), 512, Endianness::BE).is_err());
    assert!(BVF::<u16, 2>::read(&mut Cursor::new(&buffer), 512, Endianness::BE).is_err());
    assert!(BVF::<u32, 2>::read(&mut Cursor::new(&buffer), 512, Endianness::BE).is_err());
    assert!(BVF::<u64, 2>::read(&mut Cursor::new(&buffer), 512, Endianness::BE).is_err());
    assert!(BVF::<u128, 2>::read(&mut Cursor::new(&buffer), 512, Endianness::BE).is_err());
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

fn append_inner<B: BitVector>(max_capacity: usize) {
    for capacity in 0..max_capacity {
        for split in 0..capacity {
            let mut bv1 = random_bv::<B>(split);
            let bv2 = random_bv::<B>(capacity - split);
            let mut bits1: Vec<Bit> = bv1.iter().collect();
            let bits2: Vec<Bit> = bv2.iter().collect();

            bv1.append(&bv2);
            bits1.extend(bits2.iter());
            for (b1, &b2) in bv1.iter().zip(bits1.iter()) {
                assert_eq!(b1, b2);
            }
        }
    }
}

#[test]
fn append_bvf() {
    bvf_inner_unroll_cap!(append_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn append_bvd() {
    append_inner::<BVD>(256);
}

#[test]
fn append_bv() {
    append_inner::<BV>(256);
}

fn prepend_inner<B: BitVector>(max_capacity: usize) {
    for capacity in 0..max_capacity {
        for split in 0..capacity {
            let mut bv1 = random_bv::<B>(split);
            let bv2 = random_bv::<B>(capacity - split);
            let bits1: Vec<Bit> = bv1.iter().collect();
            let mut bits2: Vec<Bit> = bv2.iter().collect();

            bv1.prepend(&bv2);
            bits2.extend(bits1.iter());
            for (b1, &b2) in bv1.iter().zip(bits2.iter()) {
                assert_eq!(b1, b2);
            }
        }
    }
}

#[test]
fn prepend_bvf() {
    bvf_inner_unroll_cap!(prepend_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn prepend_bvd() {
    prepend_inner::<BVD>(256);
}

#[test]
fn prepend_bv() {
    prepend_inner::<BV>(256);
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

fn leading_zeros_inner<B: BitVector>(max_capacity: usize) {
    let mut rng = thread_rng();
    assert_eq!(B::zeros(0).leading_zeros(), 0);
    for capacity in 1..max_capacity {
        let split = rng.gen_range(0..capacity);
        let mut bv = B::ones(split);
        bv.resize(capacity, Bit::Zero);
        assert_eq!(bv.leading_zeros(), capacity - split);
    }
}

#[test]
fn leading_zeros_bvf() {
    bvf_inner_unroll_cap!(leading_zeros_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn leading_zeros_bvd() {
    leading_zeros_inner::<BVD>(256);
}

#[test]
fn leading_zeros_bv() {
    leading_zeros_inner::<BV>(256);
}

fn leading_ones<B: BitVector>(max_capacity: usize) {
    let mut rng = thread_rng();
    assert_eq!(B::zeros(0).leading_ones(), 0);
    for capacity in 1..max_capacity {
        let split = rng.gen_range(0..capacity);
        let mut bv = B::zeros(split);
        bv.resize(capacity, Bit::One);
        assert_eq!(bv.leading_ones(), capacity - split);
    }
}

#[test]
fn leading_ones_bvf() {
    bvf_inner_unroll_cap!(leading_ones, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn leading_ones_bvd() {
    leading_ones::<BVD>(256);
}

#[test]
fn leading_ones_bv() {
    leading_ones::<BV>(256);
}

fn trailing_zeros_inner<B: BitVector>(max_capacity: usize) {
    let mut rng = thread_rng();
    assert_eq!(B::zeros(0).trailing_zeros(), 0);
    for capacity in 1..max_capacity {
        let split = rng.gen_range(0..capacity);
        let mut bv = B::zeros(split);
        bv.resize(capacity, Bit::One);
        assert_eq!(bv.trailing_zeros(), split);
    }
}

#[test]
fn trailing_zeros_bvf() {
    bvf_inner_unroll_cap!(trailing_zeros_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn trailing_zeros_bvd() {
    trailing_zeros_inner::<BVD>(256);
}

#[test]
fn trailing_zeros_bv() {
    trailing_zeros_inner::<BV>(256);
}

fn trailing_ones<B: BitVector>(max_capacity: usize) {
    let mut rng = thread_rng();
    assert_eq!(B::zeros(0).trailing_ones(), 0);
    for capacity in 1..max_capacity {
        let split = rng.gen_range(0..capacity);
        let mut bv = B::ones(split);
        bv.resize(capacity, Bit::Zero);
        assert_eq!(bv.trailing_ones(), split);
    }
}

#[test]
fn trailing_ones_bvf() {
    bvf_inner_unroll_cap!(trailing_ones, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn trailing_ones_bvd() {
    trailing_ones::<BVD>(256);
}

#[test]
fn trailing_ones_bv() {
    trailing_ones::<BV>(256);
}

fn significant_bits_inner<B: BitVector>(max_capacity: usize) {
    for capacity in 0..max_capacity {
        let bv = random_bv::<B>(capacity);
        assert_eq!(
            bv.copy_range(bv.significant_bits()..bv.len()),
            B::zeros(bv.len() - bv.significant_bits())
        );
        if bv.significant_bits() != 0 {
            assert_ne!(
                bv.copy_range(0..bv.significant_bits()),
                B::zeros(bv.significant_bits())
            );
        }
    }
}

#[test]
fn significant_bits_bvf() {
    bvf_inner_unroll_cap!(significant_bits_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn significant_bits_bvd() {
    significant_bits_inner::<BVD>(256);
}

#[test]
fn significant_bits_bv() {
    significant_bits_inner::<BV>(256);
}

fn is_zero_inner<B: BitVector>(max_capacity: usize) {
    for capacity in 1..max_capacity {
        let bv = B::zeros(capacity);
        assert!(bv.is_zero());
        let bv = B::ones(capacity);
        assert!(!bv.is_zero());
    }
}

#[test]
fn is_zero_bvf() {
    bvf_inner_unroll_cap!(is_zero_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn is_zero_bvd() {
    is_zero_inner::<BVD>(256);
}

#[test]
fn is_zero_bv() {
    is_zero_inner::<BV>(256);
}

fn div_rem_inner<B: BitVector>(max_capacity: usize)
where
    B: for<'a> TryFrom<&'a B, Error: std::fmt::Debug>,
    for<'a> &'a B: std::ops::Mul<&'a B, Output = B>,
    B: for<'a> std::ops::Add<&'a B, Output = B>,
{
    for capacity in 1..max_capacity {
        let dividend = random_bv::<B>(capacity);
        let mut divisor = random_bv::<B>(capacity);
        while divisor.is_zero() {
            divisor = random_bv::<B>(capacity);
        }

        let (quotient, remainder) = dividend.div_rem(&divisor);
        assert_eq!(dividend, &quotient * &divisor + &remainder);
        assert!(remainder < divisor);
    }
}

#[test]
fn div_rem_bvf() {
    bvf_inner_unroll_cap!(div_rem_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn div_rem_bvd() {
    div_rem_inner::<BVD>(256);
}

#[test]
fn div_rem_bv() {
    div_rem_inner::<BV>(256);
}
