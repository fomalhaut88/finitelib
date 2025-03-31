//! Montgomery representation of Galois field with prime characteristic over
//! `Bigi` datatype.
//! (<https://en.wikipedia.org/wiki/Montgomery_modular_multiplication>).
//!
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::bigi::montgomery::Montgomery;
//!
//! // U256 datatype
//! type U256 = bigi_of_bits!(256);
//!
//! // Prime characteristic
//! let n = U256::from_hex(
//!     "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
//! );
//!
//! // Two arbitrary numbers
//! let a = U256::from_hex(
//!     "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
//! );
//! let b = U256::from_hex(
//!     "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
//! );
//!
//! // Create a Montgomery field of characteristic n and power 255
//! let mgr = Montgomery::new(n.clone(), 255);
//!
//! // Convert to Montgomery representation
//! let ai = mgr.convert_into(&a);
//! let bi = mgr.convert_into(&b);
//!
//! // Montgomery product
//! let ci = mgr.mul(&ai, &bi);
//!
//! // Convert back
//! let c = mgr.convert_from(&ci);
//!
//! // Check that it corresponds to modular product
//! assert_eq!(c, bigi_ring_of_bits!(256).mulrem(&a, &b, &n));
//! ```

use crate::bigi::{Bigi, BIGI_UNIT_BITS};
use crate::bigi::rings::BigiRing;
use crate::ring::EuclideanRing;
use crate::field::Field;


/// Galois prime field `GF(p)` in the Montgomery representation.
///
/// See [crate::bigi::montgomery] for the full example.
#[derive(Debug, Clone)]
pub struct Montgomery<const N: usize> {
    ring: BigiRing<N>,
    characteristic: Bigi<N>,
    power: usize,
    ni: Bigi<N>,
    e: Bigi<N>,
    e3: Bigi<N>,
}


impl<const N: usize> Montgomery<N> {
    /// Create a new Montgomery field of given characteristic. `power` must
    /// satisfy `characteristic < 2^power` and `power < N * 64`.
    pub fn new(characteristic: Bigi<N>, power: usize) -> Self {
        let ring = BigiRing::<N>;

        let r = &Bigi::<N>::from(1) << power;

        let ni = {
            let mut ni = ring.euclidean_extended(&r, &characteristic).2;
            ring.neg_assign(&mut ni);
            ni
        };

        let e = {
            let mut e = r;
            ring.divrem(&mut e, &characteristic);
            e
        };

        let e3 = {
            let mut e3 = e.clone();
            ring.mulrem_assign(&mut e3, &e, &characteristic);
            ring.mulrem_assign(&mut e3, &e, &characteristic);
            e3
        };

        Self { ring, characteristic, power, ni, e, e3 }
    }

    /// Get ring.
    pub fn ring(&self) -> &BigiRing<N> {
        &self.ring
    }

    /// Get characteristic.
    pub fn characteristic(&self) -> &Bigi<N> {
        &self.characteristic
    }

    /// Convert the number into montgomery representation.
    pub fn convert_into(&self, a: &Bigi<N>) -> Bigi<N> {
        self.ring.mulrem(a, &self.e, &self.characteristic)
    }

    /// Convert the number from montgomery representation.
    pub fn convert_from(&self, a: &Bigi<N>) -> Bigi<N> {
        self.mul(a, &self.ring.one())
    }
}


impl<const N: usize> Field for Montgomery<N> {
    type Item = Bigi<N>;

    fn zero(&self) -> Self::Item {
        self.ring.zero()
    }

    fn one(&self) -> Self::Item {
        self.e.clone()
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        a == b
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        if self.ring.is_zero(a) {
            self.ring.zero()
        } else {
            &self.characteristic - a
        }
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        self.ring.neg_assign(a)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.addrem(a, b, &self.characteristic)
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.addrem_assign(a, b, &self.characteristic);
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.subrem(a, b, &self.characteristic)
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.subrem_assign(a, b, &self.characteristic);
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let (mut u, mut v) = a.mul_overflowing(b);

        let mut t = u.clone();
        t *= &self.ni;
        t.rem_2k(self.power);
        let (t, w) = t.mul_overflowing(&self.characteristic);

        let ovf = u.add_overflowing(&t);

        if ovf {
            v.add_unit(1);
        }
        v += &w;

        u >>= self.power;
        u |= &(&v << (N * BIGI_UNIT_BITS - self.power));

        if u >= self.characteristic {
            u -= &self.characteristic;
        }

        u
    }

    fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
        if self.ring.is_zero(a) {
            None
        } else {
            let mut s = self.ring.euclidean_extended(a, &self.characteristic).1;
            if s >= self.characteristic {
                s += &self.characteristic;
            }
            Some(self.mul(&self.e3, &s))
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;
    use crate::gf::prime::Prime;
    use test::Bencher;

    #[test]
    fn test() {
        type U256 = bigi_of_bits!(256);

        let n = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );
        let k = 255;

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let b = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        let mgr = Montgomery::new(n.clone(), k);

        let ai = mgr.convert_into(&a);
        let a2 = mgr.convert_from(&ai);
        assert_eq!(a, a2);

        let bi = mgr.convert_into(&b);
        let b2 = mgr.convert_from(&bi);
        assert_eq!(b, b2);

        let ci = mgr.mul(&ai, &bi);
        assert_eq!(mgr.div(&ci, &ai), Some(bi.clone()));
        assert_eq!(mgr.div(&ci, &bi), Some(ai.clone()));

        let r256 = bigi_ring_of_bits!(256);
        let c = r256.mulrem(&a, &b, &n);
        assert_eq!(c, mgr.convert_from(&ci));
        assert_eq!(ci, mgr.convert_into(&c));

        let m = &n - &U256::from(1);
        assert_eq!(mgr.pow_scalar(&a, m.bit_iter()), mgr.one());
        assert_eq!(mgr.pow_scalar(&b, m.bit_iter()), mgr.one());
        assert_eq!(mgr.pow_scalar(&c, m.bit_iter()), mgr.one());
    }

    #[bench]
    fn bench_convert_into_255(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let mgr = Montgomery::new(characteristic, 255);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );

        bencher.iter(|| {
            let _ = mgr.convert_into(&a);
        });
    }

    #[bench]
    fn bench_convert_from_255(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let mgr = Montgomery::new(characteristic, 255);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let ai = mgr.convert_into(&a);

        bencher.iter(|| {
            let _ = mgr.convert_from(&ai);
        });
    }

    #[bench]
    fn bench_add_255(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let mgr = Montgomery::new(characteristic, 255);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let b = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        let ai = mgr.convert_into(&a);
        let bi = mgr.convert_into(&b);

        bencher.iter(|| {
            let _ = mgr.add(&ai, &bi);
        });
    }

    #[bench]
    fn bench_sub_255(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let mgr = Montgomery::new(characteristic, 255);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let b = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        let ai = mgr.convert_into(&a);
        let bi = mgr.convert_into(&b);

        bencher.iter(|| {
            let _ = mgr.sub(&ai, &bi);
        });
    }

    #[bench]
    fn bench_mul_255(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let mgr = Montgomery::new(characteristic, 255);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let b = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        let ai = mgr.convert_into(&a);
        let bi = mgr.convert_into(&b);

        bencher.iter(|| {
            let _ = mgr.mul(&ai, &bi);
        });
    }

    #[bench]
    fn bench_div_255(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let mgr = Montgomery::new(characteristic, 255);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let b = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        let ai = mgr.convert_into(&a);
        let bi = mgr.convert_into(&b);

        bencher.iter(|| {
            let _ = mgr.div(&ai, &bi);
        });
    }

    #[bench]
    fn bench_pow_scalar_255(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let mgr = Montgomery::new(characteristic, 255);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let p = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        let ai = mgr.convert_into(&a);

        bencher.iter(|| {
            let _ = mgr.pow_scalar(&ai, p.bit_iter());
        });
    }

    #[bench]
    fn bench_mul_255_gf_compare(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let r256 = bigi_ring_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let gf = Prime::new(r256, characteristic);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let b = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        bencher.iter(|| {
            let _ = gf.mul(&a, &b);
        });
    }

    #[bench]
    fn bench_div_255_gf_compare(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let r256 = bigi_ring_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let gf = Prime::new(r256, characteristic);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let b = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        bencher.iter(|| {
            let _ = gf.div(&a, &b);
        });
    }

    #[bench]
    fn bench_pow_scalar_255_gf_compare(bencher: &mut Bencher) {
        type U256 = bigi_of_bits!(256);
        let r256 = bigi_ring_of_bits!(256);
        let characteristic = U256::from_hex(
            "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED"
        );

        let gf = Prime::new(r256, characteristic);

        let a = U256::from_hex(
            "37646626CB303A9EEBAAD078ACD5632862232A27EF6426CC7D7A92251FBFEE94"
        );
        let p = U256::from_hex(
            "512BF81462535B76AFA05824673FA8A3AEDC030B7D3BB354B1A7463191134609"
        );

        bencher.iter(|| {
            let _ = gf.pow_scalar(&a, p.bit_iter());
        });
    }
}
