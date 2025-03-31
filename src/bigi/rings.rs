//! Euclidean ring over the type `Bigi` that is compatible with Galois fields.
//!
//! It implements common and modular operations, division with remainder.
//! Since algorithms are optimized by memory, it handles inner overflows, so
//! there will be no overflows in cases like modular product by a modulo even
//! if the product itself without modulo takes more memory than `Bigi` may
//! keep.

use crate::ring::EuclideanRing;
use crate::bigi::Bigi;


/// A ring for `Bigi`.
#[derive(Debug, Clone)]
pub struct BigiRing<const N: usize>;


/// Define `BigiRing` (a ring for `Bigi` numbers) from the number of bits.
#[macro_export]
macro_rules! bigi_ring_of_bits {
    ($bits:expr) => {
        BigiRing::<{ $bits / BIGI_UNIT_BITS }>
    };
}


/// Define `BigiRing` (a ring for `Bigi` numbers) from the type `Bigi`.
#[macro_export]
macro_rules! bigi_ring_for_bigi {
    ($type:ident) => {
        BigiRing::<{ std::mem::size_of::<$type>() / BIGI_UNIT_BYTES }>
    };
}


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
        let ovf = a.add_overflowing(b);
        if ovf || (*a >= *m) {
            *a -= m;
        }
    }

    fn subrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        let ovf = a.sub_overflowing(b);
        if ovf {
            *a += m;
        }
    }

    fn mulrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        *a = self.mulrem(a, b, m);
    }
}


/// A ring for `Bigi` regarding the XOR arithmetic.
#[derive(Debug)]
pub struct BigiXorRing<const N: usize>;


/// Define `BigiXorRing` (a ring for `Bigi` numbers) from the number of bits.
#[macro_export]
macro_rules! bigi_xor_ring_of_bits {
    ($bits:expr) => {
        BigiXorRing::<{ $bits / BIGI_UNIT_BITS }>
    };
}


/// Define `BigiXorRing` (a ring for `Bigi` numbers) from the type `Bigi`.
#[macro_export]
macro_rules! bigi_xor_ring_for_bigi {
    ($type:ident) => {
        BigiXorRing::<{ std::mem::size_of::<$type>() / BIGI_UNIT_BYTES }>
    };
}


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
        a.xor_mul_overflowing(b).0
    }

    fn mul_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a = self.mul(a, b);
    }

    fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> 
            Option<Self::Item> {
        let mut ext = self.zero();
        a.xor_divide_overflowing(b, &mut ext)
    }

    fn mulrem(&self, a: &Self::Item, b: &Self::Item, m: &Self::Item) -> 
            Self::Item {
        let (mut r, mut e) = a.xor_mul_overflowing(b);
        r.xor_divide_overflowing(m, &mut e).unwrap();
        r
    }

    fn mulrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        *a = self.mulrem(a, b, m);
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

    #[test]
    fn test_bigi_xor_ring() {
        // Numbers
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
        let b = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );
        let c = Bigi::<4>::from_decimal(
            "97324838896549275218599064570814530797375184017512326201551998650713089047096"
        );

        // Addition
        assert_eq!(
            BigiXorRing.add(&a, &b),
            Bigi::<4>::from_decimal(
                "31691850252084956879974018824580514582481353306169090699058036066441831533154"
            ) 
        );

        // Multiplication
        let mut d = BigiXorRing.mul(&Bigi::<8>::from(&a), &Bigi::<8>::from(&b));

        assert_eq!(
            d,
            Bigi::<8>::from_decimal(
                "5270453637307759772600222689816724241368093142259099532138447032940019039951244434061523646808416342117288405510808930047117362651398983326809124141481491"
            ) 
        );

        // Distributive property: a * b + a * c = a * (b + c)
        assert_eq!(
            BigiXorRing.add(
                &BigiXorRing.mul(&Bigi::<8>::from(&a), &Bigi::<8>::from(&b)), 
                &BigiXorRing.mul(&Bigi::<8>::from(&a), &Bigi::<8>::from(&c)),
            ),
            BigiXorRing.mul(
                &Bigi::<8>::from(&a),
                &BigiXorRing.add(&Bigi::<8>::from(&b), &Bigi::<8>::from(&c)),
            )
        );

        // Add remainder before division
        BigiXorRing.add_assign(&mut d, &Bigi::from(25));

        // Division
        let e = BigiXorRing.divrem(&mut d, &Bigi::<8>::from(&b)).unwrap();

        assert_eq!(d, Bigi::<8>::from(25));
        assert_eq!(e, Bigi::<8>::from(&a));
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
