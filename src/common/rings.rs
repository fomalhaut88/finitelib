//! Rings over common Rust integer data types.

use crate::ring::EuclideanRing;
use crate::utils;


macro_rules! define_integer_euclidean_ring {
    ($name:ident, $type:ident) => {
        /// EuclideanRing over integer.
        #[derive(Debug)]
        pub struct $name;

        impl EuclideanRing for $name {
            type Item = $type;

            fn zero(&self) -> Self::Item {
                0
            }

            fn one(&self) -> Self::Item {
                1
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

            fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a - b
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

            fn neg_assign(&self, a: &mut Self::Item) {
                *a = -*a;
            }

            fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> 
                    Option<Self::Item> {
                if *b == 0 {
                    None
                } else {
                    let q = a.div_euclid(*b);
                    *a -= q * b;
                    Some(q)
                }
            }
        }
    };
}


macro_rules! define_xor_euclidean_ring {
    ($name:ident, $type:ident) => {
        /// EuclideanRing over integer with XOR addition.
        #[derive(Debug)]
        pub struct $name;

        impl EuclideanRing for $name {
            type Item = $type;

            fn zero(&self) -> Self::Item {
                0
            }

            fn one(&self) -> Self::Item {
                1
            }

            fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
                a == b
            }

            fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a ^ b
            }

            fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                let mut b = *b;
                let mut r = 0;
                let mut e = 1;
                for _ in 0..(std::mem::size_of::<$type>() << 3) {
                    if (a & e) != 0 {
                        r ^= b;
                    }
                    b <<= 1;
                    e <<= 1;
                }
                r
            }

            fn neg(&self, a: &Self::Item) -> Self::Item {
                *a
            }

            fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
                a ^ b
            }

            fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
                *a ^= b
            }

            fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
                *a ^= b
            }

            fn mul_assign(&self, a: &mut Self::Item, b: &Self::Item) {
                *a = self.mul(a, b);
            }

            fn neg_assign(&self, _a: &mut Self::Item) {}

            fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> 
                    Option<Self::Item> {
                let order_a = utils::uint_bit_order(a);
                let order_b = utils::uint_bit_order(b);

                if order_b > 0 {
                    if order_a > 0 {
                        if order_a >= order_b {
                            let order_r = order_a - order_b;

                            let mut r = 0;
                            let mut b = b << order_r;
                            let mut ea = 1 << (order_a - 1);
                            let mut er = 1 << order_r;

                            for _ in 0..=order_r {
                                if (*a & ea) != 0 {
                                    r |= er;
                                    *a ^= b;
                                }

                                b >>= 1;
                                ea >>= 1;
                                er >>= 1;
                            }

                            Some(r)
                        } else {
                            Some(0)
                        }
                    } else {
                        Some(0)
                    }
                } else {
                    None
                }
            }
        }
    };
}


define_integer_euclidean_ring!(Ri8, i8);
define_integer_euclidean_ring!(Ri16, i16);
define_integer_euclidean_ring!(Ri32, i32);
define_integer_euclidean_ring!(Ri64, i64);
define_integer_euclidean_ring!(Ri128, i128);

define_xor_euclidean_ring!(RXu8, u8);
define_xor_euclidean_ring!(RXu16, u16);
define_xor_euclidean_ring!(RXu32, u32);
define_xor_euclidean_ring!(RXu64, u64);
define_xor_euclidean_ring!(RXu128, u128);


#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;
    use rand::Rng;

    #[test]
    fn test_ri32() {
        assert_eq!(Ri32.zero(), 0);
        assert_eq!(Ri32.one(), 1);
        assert_eq!(Ri32.eq(&3, &3), true);
        assert_eq!(Ri32.add(&3, &5), 8);
        assert_eq!(Ri32.mul(&3, &5), 15);
        assert_eq!(Ri32.neg(&3), -3);
    }

    #[test]
    fn test_rxu32() {
        assert_eq!(RXu32.zero(), 0);
        assert_eq!(RXu32.one(), 1);
        assert_eq!(RXu32.eq(&3, &3), true);
        assert_eq!(RXu32.add(&3, &5), 6);
        assert_eq!(RXu32.mul(&3, &6), 10);
        assert_eq!(RXu32.mul(&5, &7), 27);
        assert_eq!(RXu32.neg(&3), 3);
    }

    #[test]
    fn test_rxu32_divrem() {
        let a = 178098;
        let b = 2451;

        let mut r = a;
        let q = RXu32.divrem(&mut r, &b).unwrap();

        assert_eq!(RXu32.add(&RXu32.mul(&q, &b), &r), a);
    }

    #[test]
    fn test_rxu32_euclidean_extended() {
        let x = 178098;
        let y = 2452;

        let (gcd, a, b) = RXu32.euclidean_extended(&x, &y);

        assert_eq!(RXu32.add(&RXu32.mul(&x, &a), &RXu32.mul(&y, &b)), gcd);
    }

    #[bench]
    fn bench_i64_euclidean_extended(b: &mut Bencher) {
        let mut rng = rand::rng();

        let x = rng.random::<i64>().abs();
        let y = rng.random::<i64>().abs();

        b.iter(|| {
            Ri64.euclidean_extended(&x, &y);
        });
    }

    #[bench]
    fn bench_rxu64_mul(b: &mut Bencher) {
        let mut rng = rand::rng();

        let x = rng.random::<u64>() >> 32;
        let y = rng.random::<u64>() >> 32;

        b.iter(|| {
            RXu64.mul(&x, &y);
        });
    }

    #[bench]
    fn bench_rxu64_euclidean_extended(b: &mut Bencher) {
        let mut rng = rand::rng();

        let x = rng.random::<u64>();
        let y = rng.random::<u64>();

        b.iter(|| {
            RXu64.euclidean_extended(&x, &y);
        });
    }
}
