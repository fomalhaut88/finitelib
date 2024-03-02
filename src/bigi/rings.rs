/// Euclidean ring over the type `Bigi` that is compatible with Galois fields.
/// It implements common and modular operations, division with remainder.
/// Since algorithms are optimized by memory, it handles inner overflows, so
/// there will be no overflows in cases like modular product by a modulo even
/// if the product itself without modulo takes more memory than `Bigi` may
/// keep.

use crate::ring::EuclideanRing;
use crate::bigi::Bigi;


#[derive(Debug)]
pub struct BigiRing<const N: usize>;


impl<const N: usize> EuclideanRing for BigiRing<N> {
    type Item = Bigi<N>;

    fn zero(&self) -> Self::Item {
        Bigi::from(0)
    }

    fn one(&self) -> Self::Item {
        Bigi::from(1)
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        a == b
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        let mut r = a.clone();
        self.neg_assign(&mut r);
        r
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        a.bitwise_not_assign();
        a.add_unit(1);
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        a + b
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a += b;
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        a - b
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a -= b;
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        a * b
    }

    fn mul_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a *= b;
    }

    fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> Option<Self::Item> {
        a.divide(b)
    }

    fn addrem(&self, a: &Self::Item, b: &Self::Item, m: &Self::Item) -> 
            Self::Item {
        let mut r = a.clone();
        self.addrem_assign(&mut r, b, m);
        r
    }

    fn subrem(&self, a: &Self::Item, b: &Self::Item, m: &Self::Item) -> 
            Self::Item {
        let mut r = a.clone();
        self.subrem_assign(&mut r, b, m);
        r
    }

    fn mulrem(&self, a: &Self::Item, b: &Self::Item, m: &Self::Item) -> 
            Self::Item {
        let (mut r, mut e) = a.mul_overflowing(b);
        r.divide_overflowing(m, &mut e).unwrap();
        r
    }

    fn addrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        *a += b;
        if (*a < *b) || (*a >= *m) {
            *a -= m;
        }
    }

    fn subrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        if *a < *b {
            *a += m;
        }
        *a -= b;
    }

    fn mulrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        *a = self.mulrem(a, b, m);
    }
}


#[derive(Debug)]
pub struct BigiXorRing<const N: usize>;


impl<const N: usize> EuclideanRing for BigiXorRing<N> {
    type Item = Bigi<N>;

    fn zero(&self) -> Self::Item {
        Bigi::from(0)
    }

    fn one(&self) -> Self::Item {
        Bigi::from(1)
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        a == b
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        a.clone()
    }

    fn neg_assign(&self, _a: &mut Self::Item) {}

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        a ^ b
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a ^= b;
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        a ^ b
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a ^= b;
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let mut b = b.clone();
        let mut r = self.zero();
        for bit in a.bit_iter() {
            if bit {
                r ^= &b;
            }
            b <<= 1;
        }
        r
    }

    fn mul_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a = self.mul(a, b);
    }

    fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> 
            Option<Self::Item> {
        let order_a = a.bit_len();
        let order_b = b.bit_len();

        if order_b > 0 {
            if order_a >= order_b {
                let order_r = order_a - order_b + 1;

                let mut r = self.zero();
                let mut b = b << order_r;

                for i in (0..order_r).rev() {
                    b >>= 1;
                    if a.bit_get(order_b + i) {
                        r.bit_set(i, true);
                        *a ^= &b;
                    }
                }

                Some(r)
            } else {
                Some(self.zero())
            }
        } else {
            None
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;

    #[test]
    fn test_powrem_scalar() {
        // Arbitrary number
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        // Prime modulo
        let m = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        // Perform a^(m - 1) mod m
        let b = BigiRing.powrem_scalar(
            &a, (&m - &Bigi::from(1)).bit_iter(), &m
        );

        // Check 1 according to Fermat's little theorem
        assert_eq!(b, Bigi::from(1));
    }

    #[bench]
    fn bench_powrem_scalar(bencher: &mut Bencher) {
        // Arbitrary number
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        // Prime modulo
        let m = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        // Power
        let k = &m - &Bigi::from(1);

        bencher.iter(|| {
            // Power
            let b = BigiRing.powrem_scalar(&a, k.bit_iter(), &m);

            // Check
            assert_eq!(b, Bigi::from(1));
        });
    }
}
