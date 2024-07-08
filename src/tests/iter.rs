use crate::auto::BV;
use crate::dynamic::BVD;
use crate::fixed::BVF;
use crate::tests::bvf_inner_unroll_cap;
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
    for _ in 0..(capacity + 1) / 2 {
        assert_eq!(it1.next().copied(), it2.next());
        assert_eq!(it1.next_back().copied(), it2.next_back());
    }
    assert_eq!(it2.next(), None);
    assert_eq!(it2.next_back(), None);
    assert_eq!(it1.last().copied(), it2.last());

    let mut it1 = bits.iter();
    let mut it2 = bv.iter();
    for _ in 0..capacity / 3 {
        assert_eq!(it1.nth(3).copied(), it2.nth(3));
        assert_eq!(it1.nth_back(3).copied(), it2.nth_back(3));
    }

    assert_eq!(bits.len(), bv.iter().count());
    assert_eq!(bits.iter().last().copied(), bv.iter().last());

    let bits2: Vec<Bit> = bv.iter().collect();
    assert_eq!(bits, bits2);
}

#[test]
fn iter_fixed() {
    bvf_inner_unroll_cap!(iter_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn iter_dynamic() {
    for capacity in 1..512 {
        iter_inner::<BVD>(capacity);
    }
}

#[test]
fn iter_auto() {
    for capacity in 1..512 {
        iter_inner::<BV>(capacity);
    }
}

fn from_iter_inner<B: BitVector + FromIterator<Bit>>(capacity: usize) {
    let mut rng = thread_rng();
    let bits: Vec<Bit> = (0..capacity)
        .map(|_| Bit::from(rng.gen::<bool>()))
        .collect();
    let bv: B = bits.iter().copied().collect();
    for (b1, &b2) in bv.iter().zip(bits.iter()) {
        assert_eq!(b1, b2);
    }
}

#[test]
fn from_iter_bvf() {
    bvf_inner_unroll_cap!(from_iter_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn from_iter_bvd() {
    from_iter_inner::<BVD>(256);
}

#[test]
fn from_iter_bv() {
    from_iter_inner::<BV>(64);
    from_iter_inner::<BV>(256);
}

fn extend_inner<B: BitVector + Extend<Bit>>(capacity: usize) {
    let mut rng = thread_rng();
    let bits: Vec<Bit> = (0..capacity)
        .map(|_| Bit::from(rng.gen::<bool>()))
        .collect();
    let mut bv = B::with_capacity(capacity / 2);
    bv.extend(bits.iter().copied());
    for (b1, &b2) in bv.iter().zip(bits.iter()) {
        assert_eq!(b1, b2);
    }
}

#[test]
fn extend_bvf() {
    bvf_inner_unroll_cap!(extend_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn extend_bvd() {
    extend_inner::<BVD>(256);
}

#[test]
fn extend_bv() {
    extend_inner::<BV>(64);
    extend_inner::<BV>(256);
}
