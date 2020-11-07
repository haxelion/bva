use crate::BitVector;
use crate::fixed::{BV8, BV16};

#[test]
fn sample() {
    let a = BV16::ones(15);
    let b = BV8::ones(7);
    assert_eq!("000000001111111", format!("{:b}", (a & b)).as_str());

    assert_eq!("000000001111110", format!("{:b}", (a + b)).as_str());
}