pub trait StaticCast<U> {
    fn cast_from(u: U) -> Self;
    fn cast_to(self) -> U;
}

macro_rules! impl_staticcast {
    ($($type:ty),+) => {
        impl_staticcast!(@as_dual {$($type),+}, {$($type),+});
    };
    (@as_dual {$($lhs:ty),+}, $rhs:tt) => {
        $(
            impl_staticcast!(@as_single $lhs, $rhs);
        )+
    };
    (@as_single $lhs:ty, {$($rhs:ty),+}) => {
        $(
            impl StaticCast<$rhs> for $lhs {
                fn cast_from(u: $rhs) -> Self {
                    u as Self
                }
                
                fn cast_to(self) -> $rhs {
                    self as $rhs
                }
            }
        )+
    };
}

impl_staticcast!(u8, u16, u32, u64, u128, usize);

pub trait Constants {
    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;
}

macro_rules! impl_constants {
    ($($type:ty),+) => {
        $(
            impl Constants for $type {
                const ZERO: Self = 0;
                const ONE: Self = 1;
                const MIN: Self = <$type>::MIN;
                const MAX: Self = <$type>::MAX;
            }
        )+
    }
}

impl_constants!(u8, u16, u32, u64, u128, usize);