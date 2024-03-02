//! Galios binary field `GF(2^m)`.

use crate::field::Field;
use crate::ring::EuclideanRing;


#[derive(Debug, Clone)]
pub struct Binary<R: EuclideanRing> {
    ring: R,
    irreducible: R::Item,
}


impl<R: EuclideanRing> Binary<R> {
    pub fn new(ring: R, irreducible: R::Item) -> Self {
        Self { ring, irreducible }
    }
}


impl<R: EuclideanRing> Field for Binary<R> {
    type Item = R::Item;

    fn zero(&self) -> Self::Item {
        self.ring.zero()
    }

    fn one(&self) -> Self::Item {
        self.ring.one()
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        self.ring.eq(a, b)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.add(a, b)
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.sub(a, b)
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let mut r = self.ring.mul(a, b);
        self.ring.divrem(&mut r, &self.irreducible);
        r
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        self.ring.neg(a)
    }

    fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
        if self.ring.is_zero(a) {
            None
        } else {
            Some(self.ring.euclidean_extended(a, &self.irreducible).1)
        }
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.add_assign(a, b);
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.sub_assign(a, b);
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        self.ring.neg_assign(a);
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;
    use rand::Rng;
    use crate::common::rings::{RXu32, RXu64};
    use crate::utils;

    #[test]
    fn test() {
        let bf = Binary::new(RXu32, 19);

        assert_eq!(bf.add(&12, &13), 1);
        assert_eq!(bf.mul(&11, &5), 1);
        assert_eq!(bf.inv(&11), Some(5));
        assert_eq!(bf.pow_scalar(&11, utils::int_to_bits_iter(15)), 1);
    }

    #[bench]
    fn bench_pow_scalar_degree32(b: &mut Bencher) {
        /*
             4 : 25
             8 : 395
            16 : 119255
            32 : 6765766665
        */
        let degree = 32;
        let mask = (1_u64 << degree) - 1;
        let bf = Binary::new(RXu64, 6765766665);

        let mut rng = rand::thread_rng();
        let x: u64 = rng.gen::<u64>() & mask;

        b.iter(|| {
            let y = bf.pow_scalar(&x, utils::int_to_bits_iter(mask));
            assert_eq!(y, 1);
        });
    }
}
