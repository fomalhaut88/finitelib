//! Fields over common Rust float data types.

use crate::field::Field;


macro_rules! define_float_field {
    ($name:ident, $type:ident) => {
        /// Field over float.
        pub struct $name;

        impl Field for $name {
            type Item = $type;

            fn zero(&self) -> Self::Item {
                0.0
            }

            fn one(&self) -> Self::Item {
                1.0
            }

            fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
                a == b
            }

            fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a + b
            }

            fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a * b
            }

            fn neg(&self, a: &Self::Item) -> Self::Item {
                - a
            }

            fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
                if *a == 0.0 { None } else { Some(1.0 / a) }
            }

            fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a - b
            }

            fn div(&self, a: &Self::Item, b: &Self::Item) 
                    -> Option<Self::Item> {
                if *b == 0.0 { None } else { Some(a / b) }
            }

            fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
                *a += *b;
            }

            fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
                *a -= *b;
            }

            fn mul_assign(&self, a: &mut Self::Item, b: &Self::Item) {
                *a *= *b;
            }

            fn div_assign(&self, a: &mut Self::Item, b: &Self::Item) {
                *a /= *b;
            }

            fn neg_assign(&self, a: &mut Self::Item) {
                *a = -*a;
            }

            fn inv_assign(&self, a: &mut Self::Item) {
                *a = 1.0 / *a;
            }
        }
    };
}


define_float_field!(Ff32, f32);
define_float_field!(Ff64, f64);


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ff32() {
        assert_eq!(Ff32.zero(), 0.0);
        assert_eq!(Ff32.one(), 1.0);
        assert_eq!(Ff32.eq(&3.25, &3.25), true);
        assert_eq!(Ff32.add(&3.25, &5.5), 8.75);
        assert_eq!(Ff32.mul(&3.25, &5.5), 17.875);
        assert_eq!(Ff32.neg(&3.25), -3.25);
        assert_eq!(Ff32.inv(&8.0), Some(0.125));
        assert_eq!(Ff32.inv(&0.0), None);
    }
}
