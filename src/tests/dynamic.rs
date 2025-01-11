use std::hash::{DefaultHasher, Hash, Hasher};

use crate::bit::Bit;
use crate::dynamic::Bvd;
use crate::tests::random_bv;
use crate::BitVector;

#[test]
fn new_into() {
    for length in 0..512 {
        let bv1 = random_bv::<Bvd>(length);
        let (data, length) = bv1.clone().into_inner();
        let bv2 = Bvd::new(data, length);
        assert_eq!(bv1, bv2);
    }
}

#[test]
fn hash() {
    for length in 0..512 {
        let bv1 = random_bv::<Bvd>(length);
        let bv2 = random_bv::<Bvd>(length);
        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();
        bv1.hash(&mut hasher1);
        bv2.hash(&mut hasher2);
        assert_eq!(hasher1.finish() == hasher2.finish(), bv1 == bv2);
    }
}

#[test]
fn shrink_to_fit_bvd() {
    let capacity = 512;
    for length in 0..capacity / 2 {
        let mut bvd = Bvd::with_capacity(capacity);
        bvd.resize(length, Bit::One);
        assert_eq!(bvd.capacity(), capacity);
        bvd.shrink_to_fit();
        assert!(bvd.capacity() < capacity);
        assert_eq!(bvd, Bvd::ones(length));
    }
}
