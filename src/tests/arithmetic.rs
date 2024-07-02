mod add {
    use std::ops::{Add, AddAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(Add::add, AddAssign::add_assign);
}

mod mul {
    use std::ops::{Mul, MulAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(Mul::mul, MulAssign::mul_assign);
}

mod sub {
    use std::ops::{Sub, SubAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(Sub::sub, SubAssign::sub_assign);
}
