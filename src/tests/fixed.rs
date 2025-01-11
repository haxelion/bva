use std::hash::{DefaultHasher, Hash, Hasher};

use crate::fixed::Bvf;
use crate::tests::{bvf_inner_unroll, random_bv};
use crate::utils::Integer;

fn new_into_inner<I: Integer, const N: usize>() {
    for length in 0..Bvf::<I, N>::capacity() {
        let bv1 = random_bv::<Bvf<I, N>>(length);
        let (data, length) = bv1.clone().into_inner();
        let bv2 = Bvf::<I, N>::new(data, length);
        assert_eq!(bv1, bv2);
    }
}

fn hash_inner<I: Integer, const N: usize>() {
    for length in 0..Bvf::<I, N>::capacity() {
        let bv1 = random_bv::<Bvf<I, N>>(length);
        let bv2 = random_bv::<Bvf<I, N>>(length);
        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();
        bv1.hash(&mut hasher1);
        bv2.hash(&mut hasher2);
        assert_eq!(hasher1.finish() == hasher2.finish(), bv1 == bv2);
    }
}

#[test]
fn new_into() {
    bvf_inner_unroll!(new_into_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}

#[test]
fn hash() {
    bvf_inner_unroll!(hash_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}
