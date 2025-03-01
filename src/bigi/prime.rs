//! Algoritms for long prime numbers.

use std::mem;

use rand::Rng;

use crate::ring::EuclideanRing;
use crate::bigi::Bigi;
use crate::bigi::rings::BigiRing;


/// Fermat random primality test. For a random generated `x`
/// such that `0 < x < z` there calculated `y = x^z mod z`. If `y` is not
/// equal to `x`, the function returns `false` and stop iterations, that
/// means `z` is not prime. Otherwise the procedure is repeated for a
/// different random `x`. There are up to `count` iterations. If all `x`
/// were prime witnesses the function returns `true`. There is optimization
/// that returns `false` if `z` is even (except `2`) and there are hard coded
/// results for `z < 4`. 
/// 
/// [https://en.wikipedia.org/wiki/Fermat_primality_test](https://en.wikipedia.org/wiki/Fermat_primality_test)
///
/// ```rust
/// use finitelib::bigi::Bigi;
/// use finitelib::bigi::prime::fermat_test;
///
/// let mut rng = rand::rng();
///
/// assert_eq!(fermat_test(&mut rng, &Bigi::<4>::from_decimal("19"), 10), true);
/// ```
pub fn fermat_test<const N: usize, R: Rng>(rng: &mut R, z: &Bigi<N>, 
                                           count: usize) -> bool {
    // Get length of the number in bits
    let bit_len = z.bit_len();

    // Return `false` for numbers 0 and 1
    if bit_len < 2 {
        false
    }
    // Return `true` for numbers 2 and 3
    else if bit_len == 2 {
        true
    }
    // Return `false` for even numbers (except 2, that is considered above)
    else if !z.bit_get(0) {
        false
    }
    // Other cases
    else {
        let mut is_prime = true;

        for _ in 0..count {
            // Random x: 0 < x < z
            let mut x = Bigi::<N>::from(0);

            while &x == &Bigi::<N>::from(0) { 
                x = rng.random();
                x.rem_2k(bit_len);
                x.divide(&z);
            }

            // Power x^z mod z
            let y = BigiRing.powrem_scalar(&x, z.bit_iter(), &z);

            // If `y` is not equal to `x`, 
            // according The Fermat's Little Theorem `z` is not prime
            if &x != &y {
                is_prime = false;
                break;
            }
        }

        is_prime
    }
}


/// Miller-Rabin random primality test. There are up to `count` iterations. 
/// If the function returns `true` and `z > 4`, the probability of prime `z` is
/// `1 - (1 / 4)^count`. 
/// 
/// [https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test](https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test)
///
/// ```rust
/// use finitelib::bigi::Bigi;
/// use finitelib::bigi::prime::miller_rabin_test;
///
/// let mut rng = rand::rng();
///
/// assert_eq!(
///     miller_rabin_test(&mut rng, &Bigi::<4>::from_decimal("19"), 10), 
///     true
/// );
/// ```
pub fn miller_rabin_test<const N: usize, R: Rng>(rng: &mut R, z: &Bigi<N>, 
                                                 count: usize) -> bool {
    // Get length of the number in bits
    let bit_len = z.bit_len();

    // Return `false` for numbers 0 and 1
    if bit_len < 2 {
        false
    }
    // Return `true` for numbers 2 and 3
    else if bit_len == 2 {
        true
    }
    // Return `false` for even numbers (except 2, that is considered above)
    else if !z.bit_get(0) {
        false
    }
    // Other cases
    else {
        // Represent z as 2^s * d
        let (s, d) = {
            let mut s = 1;
            while !z.bit_get(s) {
                s += 1;
            }
            (s, z >> s)
        };

        // Result variable
        let mut is_prime = true;

        for _ in 0..count {
            // Random x: 0 < x < z
            let mut x = Bigi::<N>::from(0);

            while &x == &Bigi::<N>::from(0) { 
                x = rng.random();
                x.rem_2k(bit_len);
                x.divide(&z);
            }

            // Power x^d mod z
            let mut y = BigiRing.powrem_scalar(&x, d.bit_iter(), &z);

            // Check x^d = 1 mod z
            if y != Bigi::from(1) {
                // let mut w;
                let mut r = 0;

                while r < s {
                    // Check x^(d * 2^r) = (-1) mod z
                    if (u64::from(z) - 1 == u64::from(&y)) && y.to_iter()
                            .zip(z.to_iter()).skip(1).all(|(a, b)| a == b) {
                        break;
                    }

                    // Double y
                    y = BigiRing.mulrem(&y, &y, &z);

                    // Increment r
                    r += 1;
                }

                // If no `r` found, `z` is not prime
                if r == s {
                    is_prime = false;
                    break;
                }
            }
        }

        is_prime
    }
}


/// Generating a pseudoprime number sized exactly `bits` bits based on
/// Miller-Rabin primality test. The probability of that the result is prime
/// is `1 - (1 / 4)^count`.
///
/// ```rust
/// use finitelib::bigi::Bigi;
/// use finitelib::bigi::prime::{gen_pseudoprime, miller_rabin_test};
///
/// let mut rng = rand::rng();
///
/// let x: Bigi<4> = gen_pseudoprime(&mut rng, 256, 10);
/// 
/// assert_eq!(miller_rabin_test(&mut rng, &x, 10), true);
/// ```
pub fn gen_pseudoprime<const N: usize, R: Rng>(rng: &mut R, bits: usize, 
                                               count: usize) -> Bigi<N> {
    loop {
        // Generate a random number sized `bits` bits
        let mut x: Bigi<N> = rng.random();
        x.rem_2k(bits);

        // Set first and last bits to 1
        x.bit_set(0, true);
        x.bit_set(bits - 1, true);

        // Check primeness
        if miller_rabin_test(rng, &x, count) {
            return x;
        }
    }
}


/// Calculates the
/// [Legendre symbol](https://en.wikipedia.org/wiki/Legendre_symbol)
/// of an integer `a` and prime `p`.
/// The algorithm was taken from  "Algorithmic Number Theory"
/// by Bach and Shallit (page 113).
///
/// ```rust
/// use finitelib::bigi::Bigi;
/// use finitelib::bigi::prime::legendre_symbol;
///
/// assert_eq!(legendre_symbol(&Bigi::<4>::from(6), &Bigi::<4>::from(137)), -1);
/// assert_eq!(legendre_symbol(&Bigi::<4>::from(8), &Bigi::<4>::from(137)), 1);
/// assert_eq!(legendre_symbol(&Bigi::<4>::from(0), &Bigi::<4>::from(137)), 0);
/// ```
pub fn legendre_symbol<const N: usize>(a: &Bigi<N>, p: &Bigi<N>) -> i32 {
    /*
    An alternative implementation as `a^((p - 1) / 2) mod p`.

    ```
    let b = BigiRing.powrem_scalar(&a, p.bit_iter().skip(1), &p);

    if b == Bigi::from(0) {
        0
    } else if b == Bigi::from(1) {
        1
    } else {
        -1
    }
    ```
    */

    if a == &Bigi::from(0) {
        0
    } else {
        let mut t = 1;
        let mut a = a.clone();
        let mut p = p.clone();

        while a != Bigi::from(0) {
            let r = u64::from(&p) & 7;
            let i = (r == 3) || (r == 5);

            let mut d = 0;
            while !a.bit_get(d) {
                d += 1;
            }

            if i && (d & 1 == 1) {
                t = -t;
            }

            a >>= d;

            mem::swap(&mut a, &mut p);

            if (r & 3 == 3) && (u64::from(&p) & 3 == 3) {
                t = -t;
            }

            a %= &p;
        }

        t
    }
}


/// Performs [Tonelli–Shanks algorithm](https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm)
/// that searches for `x` such that `x^2 == n mod p` where `p` is prime
/// (modular square root). The functions returns one of the root, the other
/// can be calculated as `p - x`.
///
/// ```rust
/// use finitelib::bigi::Bigi;
/// use finitelib::bigi::prime::sqrtrem;
///
/// assert_eq!(
///     sqrtrem(&Bigi::<4>::from(8), &Bigi::<4>::from(137)),
///     Some(Bigi::<4>::from(75))
/// );
/// assert_eq!(
///     sqrtrem(&Bigi::<4>::from(6), &Bigi::<4>::from(137)),
///     None
/// );
/// ```
pub fn sqrtrem<const N: usize>(n: &Bigi<N>, p: &Bigi<N>) -> Option<Bigi<N>> {
    // Calculate Legendre symbol
    match legendre_symbol(&n, &p) {
        0 => Some(Bigi::from(0)),
        -1 => None,
        _ => {
            // Case p = 3 (mod 4)
            if u64::from(p) & 3 == 3 {
                // n^((p + 1) / 4)
                let mut r = BigiRing.powrem_scalar(
                    &n, p.bit_iter().skip(2), &p
                );
                BigiRing.mulrem_assign(&mut r, &n, &p);

                Some(r)
            } 
            // Case p = 1 (mod 4)
            else {
                // Defining q and s such that p - 1 = q * 2^s
                let (q, s) = {
                    let mut s = 1;
                    while !p.bit_get(s) {
                        s += 1;
                    }
                    (p >> s, s)
                };

                // Searching for a non-quadratic residue
                let z = {
                    let mut z = Bigi::<N>::from(2);
                    loop {
                        if legendre_symbol(&z, &p) == -1 {
                            break;
                        }

                        // We add 3, because `x^2 != 2 mod 3` for any `x`,
                        // so `z` is never a square. Thus `z` is more likely
                        // a non-quadratic residue.
                        z.add_unit(3);  
                    }
                    z
                };

                // c = z^q mod p
                let mut c = BigiRing.powrem_scalar(&z, q.bit_iter(), &p);

                // r = n^((q + 1) / 2) mod p
                let mut r = BigiRing.powrem_scalar(
                    &n, q.bit_iter().skip(1), &p
                );
                BigiRing.mulrem_assign(&mut r, &n, &p);

                // t = n^q mod p
                let mut t = BigiRing.powrem_scalar(&n, q.bit_iter(), &p);

                // m = s
                let mut m = s;

                // Tonelli–Shanks's loop
                while t != Bigi::from(1) {
                    let i = {
                        let mut tp = t.clone();
                        let mut i = 0;
                        while tp != Bigi::from(1) {
                            tp = BigiRing.mulrem(&tp, &tp, &p);
                            i += 1;
                        }
                        i
                    };

                    let b = BigiRing.powrem_scalar(
                        &c, (&Bigi::<N>::from(1) << (m - i - 1)).bit_iter(), &p
                    );

                    r = BigiRing.mulrem(&r, &b, &p);
                    c = BigiRing.mulrem(&b, &b, &p);
                    t = BigiRing.mulrem(&t, &c, &p);

                    m = i;
                }

                Some(r)
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;

    #[test]
    fn test_fermat_test() {
        let mut rng = rand::rng();

        assert_eq!(
            fermat_test(
                &mut rng, 
                &Bigi::<4>::from_decimal(
                    "99893747326269902623342789505183727815353444030279517503290826441538462138393"
                ), 
                10
            ), true
        );

        assert_eq!(
            fermat_test(
                &mut rng, 
                &Bigi::<4>::from_decimal(
                    "70011597082245702521290087447806528763417035600728176437530042129660745583227"
                ), 
                10
            ), false
        );

        assert_eq!(
            fermat_test(&mut rng, &Bigi::<4>::from_decimal("2"), 10), true
        );

        assert_eq!(
            fermat_test(&mut rng, &Bigi::<4>::from_decimal("1"), 10), false
        );

        assert_eq!(
            fermat_test(&mut rng, &Bigi::<4>::from_decimal("5"), 10), true
        );

        assert_eq!(
            fermat_test(&mut rng, &Bigi::<4>::from_decimal("9"), 10), false 
        );

        assert_eq!(
            fermat_test(&mut rng, &Bigi::<4>::from_decimal("11"), 10), true
        );
    }

    #[test]
    fn test_miller_rabin_test() {
        let mut rng = rand::rng();

        assert_eq!(
            miller_rabin_test(
                &mut rng, 
                &Bigi::<4>::from_decimal(
                    "99893747326269902623342789505183727815353444030279517503290826441538462138393"
                ), 
                10
            ), true
        );

        assert_eq!(
            miller_rabin_test(
                &mut rng, 
                &Bigi::<4>::from_decimal(
                    "70011597082245702521290087447806528763417035600728176437530042129660745583227"
                ), 
                10
            ), false
        );

        assert_eq!(
            miller_rabin_test(&mut rng, &Bigi::<4>::from_decimal("2"), 10), true
        );

        assert_eq!(
            miller_rabin_test(&mut rng, &Bigi::<4>::from_decimal("1"), 10), false
        );

        assert_eq!(
            miller_rabin_test(&mut rng, &Bigi::<4>::from_decimal("5"), 10), true
        );

        assert_eq!(
            miller_rabin_test(&mut rng, &Bigi::<4>::from_decimal("9"), 10), false 
        );

        assert_eq!(
            miller_rabin_test(&mut rng, &Bigi::<4>::from_decimal("11"), 10), true
        );
    }

    #[test]
    fn test_legendre_symbol() {
        let p = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        let b = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583229"
        );

        assert_eq!(legendre_symbol(&a, &p), 1);
        assert_eq!(legendre_symbol(&b, &p), -1);
        assert_eq!(legendre_symbol(&Bigi::from(0), &p), 0);
    }

    #[test]
    fn test_sqrtrem() {
        let p = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        let b = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583229"
        );

        let r = sqrtrem(&a, &p).unwrap();
        assert_eq!(BigiRing::<4>.mulrem(&r, &r, &p), a);

        assert_eq!(sqrtrem(&b, &p), None);
        assert_eq!(sqrtrem(&Bigi::<4>::from(0), &p), Some(Bigi::<4>::from(0)));
    }

    #[test]
    fn test_sqrtrem_case_3mod4() {
        let p = Bigi::<4>::from_decimal(
            "67096435317933606252190858377894931905843553631817376158639971807689379094463"
        );

        let a = Bigi::<4>::from_decimal(
            "20011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        let r = sqrtrem(&a, &p).unwrap();
        assert_eq!(BigiRing::<4>.mulrem(&r, &r, &p), a);
    }

    #[test]
    fn test_sqrtrem_bug_1() {
        let p = Bigi::<4>::from_decimal(
            "57896044618658097711785492504343953926634992332820282019728792003956564819949"
        );

        let a = Bigi::<4>::from_decimal(
            "55827520314971205986850592395192206020226125515040097182204534991281654975746"
        );

        let r = sqrtrem(&a, &p).unwrap();
        assert_eq!(BigiRing::<4>.mulrem(&r, &r, &p), a);
    }

    #[bench]
    fn bench_fermat_test(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        bencher.iter(|| {
            let _is_prime = fermat_test(&mut rng, &a, 100);
        });
    }

    #[bench]
    fn bench_miller_rabin_test(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        bencher.iter(|| {
            let _is_prime = miller_rabin_test(&mut rng, &a, 100);
        });
    }

    #[bench]
    fn bench_gen_pseudoprime(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        bencher.iter(|| {
            let _x: Bigi<4> = gen_pseudoprime(&mut rng, 256, 100);
        });
    }

    #[bench]
    fn bench_legendre_symbol(bencher: &mut Bencher) {
        let p = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        bencher.iter(|| {
            let _l = legendre_symbol(&a, &p);
        });
    }

    #[bench]
    fn bench_legendre_symbol_naive(bencher: &mut Bencher) {
        let p = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        bencher.iter(|| {
            let _l = BigiRing::<4>.powrem_scalar(&a, p.bit_iter().skip(1), &p);
        });
    }

    #[bench]
    fn bench_sqrtrem(bencher: &mut Bencher) {
        let p = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        bencher.iter(|| {
            let _r = sqrtrem(&a, &p).unwrap();
        });
    }

    #[bench]
    fn bench_sqrtrem_case_3mod4(bencher: &mut Bencher) {
        let p = Bigi::<4>::from_decimal(
            "67096435317933606252190858377894931905843553631817376158639971807689379094463"
        );

        let a = Bigi::<4>::from_decimal(
            "20011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        bencher.iter(|| {
            let _r = sqrtrem(&a, &p).unwrap();
        });
    }
}
