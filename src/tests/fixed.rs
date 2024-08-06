use crate::fixed::BVF;
use crate::tests::{bvf_inner_unroll, random_bv};
use crate::utils::Integer;

fn new_into_inner<I: Integer, const N: usize>() {
    for length in 0..BVF::<I, N>::capacity() {
        let bv1 = random_bv::<BVF<I, N>>(length);
        let (data, length) = bv1.clone().into_inner();
        let bv2 = BVF::<I, N>::new(data, length);
        assert_eq!(bv1, bv2);
    }
}

#[test]
fn new_into() {
    bvf_inner_unroll!(new_into_inner, {u8, u16, u32, u64, u128}, {1, 2, 3, 4, 5});
}
