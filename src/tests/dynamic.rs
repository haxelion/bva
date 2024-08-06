use crate::auto::BV;
use crate::bit::Bit;
use crate::dynamic::BVD;
use crate::BitVector;

#[test]
fn shrink_to_fit_bvd() {
    let capacity = 512;
    for length in 0..capacity / 2 {
        let mut bvd = BVD::with_capacity(capacity);
        bvd.resize(length, Bit::One);
        assert_eq!(bvd.capacity(), capacity);
        bvd.shrink_to_fit();
        assert!(bvd.capacity() < capacity);
        assert_eq!(bvd, BVD::ones(length));
    }
}

#[test]
fn shrink_to_fit_bv() {
    let capacity = 512;
    for length in 0..capacity / 2 {
        let mut bv = BV::with_capacity(capacity);
        bv.resize(length, Bit::One);
        assert_eq!(bv.capacity(), capacity);
        bv.shrink_to_fit();
        assert!(bv.capacity() < capacity);
        assert_eq!(bv, BV::ones(length));
    }
}
