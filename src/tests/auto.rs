use crate::auto::Bv;
use crate::bit::Bit;
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
