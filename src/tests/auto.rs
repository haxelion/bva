use std::hash::{DefaultHasher, Hash, Hasher};

use crate::auto::Bv;
use crate::bit::Bit;
use crate::tests::random_bv;
use crate::BitVector;

#[test]
fn shrink_to_fit_bv() {
    let capacity = 512;
    for length in 0..capacity / 2 {
        let mut bv = Bv::with_capacity(capacity);
        bv.resize(length, Bit::One);
        assert_eq!(bv.capacity(), capacity);
        bv.shrink_to_fit();
        assert!(bv.capacity() < capacity);
        assert_eq!(bv, Bv::ones(length));
    }
}

#[test]
fn hash() {
    for length in 0..512 {
        let bv1 = random_bv::<Bv>(length);
        let bv2 = random_bv::<Bv>(length);
        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();
        bv1.hash(&mut hasher1);
        bv2.hash(&mut hasher2);
        assert_eq!(hasher1.finish() == hasher2.finish(), bv1 == bv2);
    }
}
