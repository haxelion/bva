mod add {
    use std::ops::{Add, AddAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(Add::add, AddAssign::add_assign, { op_test_block, op_test_block2 });
}

mod div {
    use std::ops::{Div, DivAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(Div::div, DivAssign::div_assign, { op_test_block2 });
}

mod sub {
    use std::ops::{Sub, SubAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(Sub::sub, SubAssign::sub_assign, { op_test_block, op_test_block2 });
}

mod mul {
    use std::ops::{Mul, MulAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(Mul::mul, MulAssign::mul_assign, { op_test_block, op_test_block2 });
}

mod rem {
    use std::ops::{Rem, RemAssign};

    use crate::tests::*;
    use crate::utils::StaticCast;

    op_test_section!(Rem::rem, RemAssign::rem_assign, { op_test_block2 });
}
