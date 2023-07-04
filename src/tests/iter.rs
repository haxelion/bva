use crate::dynamic::BVN;
use crate::fixed::BV;
use crate::utils::Integer;
use crate::{Bit, BitVector};

use rand::{thread_rng, Rng};

fn iter_inner<B: BitVector>(capacity: usize) {
    let mut rng = thread_rng();
    let bits: Vec<Bit> = (0..capacity)
        .map(|_| Bit::from(rng.gen::<bool>()))
        .collect();
    let mut bv = B::with_capacity(capacity);
    bits.iter().for_each(|b| bv.push(*b));

    for (a, b) in bits.iter().zip(bv.iter()) {
        assert_eq!(*a, b);
    }

    for (a, b) in bits.iter().rev().zip(bv.iter().rev()) {
        assert_eq!(*a, b);
    }

    let mut it1 = bits.iter();
    let mut it2 = bv.iter();
    for _ in 0..capacity / 2 {
        assert_eq!(it1.next().copied(), it2.next());
        assert_eq!(it1.next_back().copied(), it2.next_back());
    }

    let mut it1 = bits.iter();
    let mut it2 = bv.iter();
    for _ in 0..capacity / 3 {
        assert_eq!(it1.nth(3).copied(), it2.nth(3));
        assert_eq!(it1.nth_back(3).copied(), it2.nth_back(3));
    }

    assert_eq!(bits.iter().count(), bv.iter().count());

    let bits2: Vec<Bit> = bv.iter().collect();
    assert_eq!(bits, bits2);
}

fn iter_fixed_inner<I: Integer, const N: usize>() {
    let capacity = BV::<I, N>::capacity();
    iter_inner::<BV<I, N>>(capacity);
}

#[test]
fn iter_fixed() {
    iter_fixed_inner::<u8, 1>();
    iter_fixed_inner::<u8, 2>();
    iter_fixed_inner::<u8, 3>();
    iter_fixed_inner::<u8, 4>();
    iter_fixed_inner::<u16, 1>();
    iter_fixed_inner::<u16, 2>();
    iter_fixed_inner::<u16, 3>();
    iter_fixed_inner::<u16, 4>();
    iter_fixed_inner::<u32, 1>();
    iter_fixed_inner::<u32, 2>();
    iter_fixed_inner::<u32, 3>();
    iter_fixed_inner::<u32, 4>();
    iter_fixed_inner::<u64, 1>();
    iter_fixed_inner::<u64, 2>();
    iter_fixed_inner::<u64, 3>();
    iter_fixed_inner::<u64, 4>();
    iter_fixed_inner::<u128, 1>();
    iter_fixed_inner::<u128, 2>();
    iter_fixed_inner::<u128, 3>();
    iter_fixed_inner::<u128, 4>();
}

#[test]
fn iter_dynamic() {
    for capacity in 1..512 {
        iter_inner::<BVN>(capacity);
    }
}
