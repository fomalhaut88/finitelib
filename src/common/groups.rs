//! Groups over common Rust data types: integer and float.

use crate::group::Group;


macro_rules! define_integer_group {
    ($name:ident, $type:ident) => {
        /// Addition group over integer.
        pub struct $name;

        impl Group for $name {
            type Item = $type;

            fn zero(&self) -> Self::Item {
                0
            }

            fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
                a == b
            }

            fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a.wrapping_add(*b)
            }

            fn neg(&self, a: &Self::Item) -> Self::Item {
                a.wrapping_neg()
            }

            fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a.wrapping_sub(*b)
            }
        }
    };
}


macro_rules! define_add_float_group {
    ($name:ident, $type:ident) => {
        /// Addition group over float.
        pub struct $name;

        impl Group for $name {
            type Item = $type;

            fn zero(&self) -> Self::Item {
                0.0
            }

            fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
                a == b
            }

            fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a + b
            }

            fn neg(&self, a: &Self::Item) -> Self::Item {
                - a
            }
        }
    };
}


macro_rules! define_mul_float_group {
    ($name:ident, $type:ident) => {
        /// Multiplication group over float.
        pub struct $name;

        impl Group for $name {
            type Item = $type;

            fn zero(&self) -> Self::Item {
                1.0
            }

            fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
                a == b
            }

            fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a * b
            }

            fn neg(&self, a: &Self::Item) -> Self::Item {
                1.0 / a
            }
        }
    };
}


define_integer_group!(Gi8, i8);
define_integer_group!(Gi16, i16);
define_integer_group!(Gi32, i32);
define_integer_group!(Gi64, i64);
define_integer_group!(Gi128, i128);
define_integer_group!(Gu8, u8);
define_integer_group!(Gu16, u16);
define_integer_group!(Gu32, u32);
define_integer_group!(Gu64, u64);
define_integer_group!(Gu128, u128);

define_add_float_group!(GAf32, f32);
define_add_float_group!(GAf64, f64);

define_mul_float_group!(GMf32, f32);
define_mul_float_group!(GMf64, f64);


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gi32() {
        assert_eq!(Gi32.zero(), 0);
        assert_eq!(Gi32.eq(&3, &3), true);
        assert_eq!(Gi32.add(&3, &5), 8);
        assert_eq!(Gi32.neg(&3), -3);
    }

    #[test]
    fn test_gu8() {
        assert_eq!(Gu8.zero(), 0);
        assert_eq!(Gu8.eq(&3, &3), true);
        assert_eq!(Gu8.add(&3, &5), 8);
        assert_eq!(Gu8.neg(&3), 253);
    }

    #[test]
    fn test_gaf32() {
        assert_eq!(GAf32.zero(), 0.0);
        assert_eq!(GAf32.eq(&3.25, &3.25), true);
        assert_eq!(GAf32.add(&3.25, &5.5), 8.75);
        assert_eq!(GAf32.neg(&3.25), -3.25);
    }

    #[test]
    fn test_gmf64() {
        assert_eq!(GMf64.zero(), 1.0);
        assert_eq!(GMf64.eq(&3.25, &3.25), true);
        assert_eq!(GMf64.add(&3.25, &5.5), 17.875);
        assert_eq!(GMf64.neg(&8.0), 0.125);
    }
}
