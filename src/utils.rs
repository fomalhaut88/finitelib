//! Additional functions and algorithms.

use std::{mem, ops, iter};


/// An implementation of [the exponentiation by squaring algorithm](https://en.wikipedia.org/wiki/Exponentiation_by_squaring).
///
/// Usage:
///
/// ```
/// use finitelib::utils;
///
/// let b = utils::exp_by_sqr(&2, [true, false, true].into_iter(), || 1, |a, b| a * b);
/// assert_eq!(b, 32);
/// ```
pub fn exp_by_sqr<T, I, E, F>(
            x: &T, bits_iter: I, one_func: E, mul_func: F) -> T
        where
            T: Clone, 
            I: Iterator<Item = bool>, 
            E: Fn() -> T, 
            F: Fn(&T, &T) -> T {
    let mut res = one_func();
    let mut sqr = x.clone();
    for bit in bits_iter {
        if bit {
            res = mul_func(&res, &sqr);
        }
        sqr = mul_func(&sqr, &sqr);
    }
    res
}


/// Iterator over bits of an integer value.
///
/// ```
/// use finitelib::utils::int_to_bits_iter;
///
/// let bits = int_to_bits_iter(25_u8).collect::<Vec<bool>>();
///
/// assert_eq!(bits, vec![true, false, false, true, true, false, false, false]);
/// ```
pub fn int_to_bits_iter<T>(x: T) -> impl Iterator<Item = bool>
        where T: Copy + PartialEq + From<u8> + 
                 ops::ShlAssign<usize> + 
                 ops::BitAnd<T, Output = T> {
    let mut countdown = mem::size_of::<T>() << 3;
    let mut e = T::from(1);
    let zero = T::from(0);

    iter::from_fn(move || {
        if countdown == 0 {
            None
        } else {
            let bit = x & e != zero;
            e <<= 1;
            countdown -= 1;
            Some(bit)
        }
    })
}


/// Returns the number of bits in the given unsigned integer.
///
/// ```
/// use finitelib::utils::uint_bit_order;
///
/// assert_eq!(uint_bit_order::<u64>(&0), 0);
/// assert_eq!(uint_bit_order::<u64>(&1), 1);
/// assert_eq!(uint_bit_order::<u64>(&2), 2);
/// assert_eq!(uint_bit_order::<u64>(&3), 2);
/// assert_eq!(uint_bit_order::<u64>(&4), 3);
/// assert_eq!(uint_bit_order::<u64>(&7), 3);
/// assert_eq!(uint_bit_order::<u64>(&8), 4);
/// assert_eq!(uint_bit_order::<u64>(&20), 5);
/// assert_eq!(uint_bit_order::<u64>(&30), 5);
/// assert_eq!(uint_bit_order::<u64>(&40), 6);
/// assert_eq!(uint_bit_order::<u64>(&100), 7);
/// assert_eq!(uint_bit_order::<u64>(&200), 8);
/// ```
pub fn uint_bit_order<T>(x: &T) -> usize where
        T: PartialOrd + From<u8>,
        for<'a> &'a T: ops::Shl<usize, Output = T> {
    let one = T::from(1);
    binary_search(
        mem::size_of::<T>() << 3,
        |i| *x >= &one << i 
    )
}


/// Build one unsigned unteger from two halves `x` and `y` that are smaller
/// unsigned integers. Note, that the size of `x` and `y` must be exactly
/// two times smaller than the size of the result, otherwise the behavior is
/// undefined.
///
/// ```rust
/// use finitelib::utils::uint_merge;
///
/// let z = uint_merge::<_, u16>(25u8, 36u8);
/// assert_eq!(z, 6436);
/// ```
pub fn uint_merge<U, V>(x: U, y: U) -> V 
        where
            V: From<U> + ops::Shl<usize, Output = V> + ops::BitOr<Output = V> {
    let offset: usize = mem::size_of::<U>() << 3;
    (V::from(x) << offset) | V::from(y)
}


/// Binary search algorithm that returns the first index 
/// for which the function `compare` returns `true`. The function must satisfy
/// `compare(i) <= compare(j)` for each `i < j`.
pub fn binary_search<F: Fn(usize) -> bool>(size: usize, compare: F) -> usize {
    let mut r = 0;

    if size > 0 {
        let mut s = size;
        while s > 1 {
            let h = s >> 1;
            if compare(r + h) {
                r += h;
            }
            s = h + (s & 1);
        }
        if compare(0) {
            r += 1;
        }
    }

    r
}


#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;
    use rand::Rng;

    #[test]
    fn test_binary_search() {
        let arr = [2, 4, 6, 6, 10, 12];

        assert_eq!(binary_search(arr.len(), |i| 0 > arr[i]), 0);
        assert_eq!(binary_search(arr.len(), |i| 2 > arr[i]), 0);
        assert_eq!(binary_search(arr.len(), |i| 3 > arr[i]), 1);
        assert_eq!(binary_search(arr.len(), |i| 4 > arr[i]), 1);
        assert_eq!(binary_search(arr.len(), |i| 6 > arr[i]), 2);
        assert_eq!(binary_search(arr.len(), |i| 7 > arr[i]), 4);
        assert_eq!(binary_search(arr.len(), |i| 10 > arr[i]), 4);
        assert_eq!(binary_search(arr.len(), |i| 11 > arr[i]), 5);
        assert_eq!(binary_search(arr.len(), |i| 12 > arr[i]), 5);
        assert_eq!(binary_search(arr.len(), |i| 13 > arr[i]), 6);
    }

    #[bench]
    fn bench_exp_by_sqr(b: &mut Bencher) {
        let mut rng = rand::rng();

        let m = rng.random::<u64>() >> 32;
        let p = rng.random::<u64>() >> 32;
        let x = rng.random::<u64>() % m;

        b.iter(|| {
            exp_by_sqr(&x, int_to_bits_iter(p), || 1, |a, b| (a * b) % m);
        });
    }

    #[bench]
    fn bench_int_to_bits(b: &mut Bencher) {
        let mut rng = rand::rng();

        let x: u64 = rng.random();

        b.iter(|| {
            let _bits = int_to_bits_iter(x).collect::<Vec<bool>>();
        });
    }

    #[bench]
    fn bench_uint_bit_order(b: &mut Bencher) {
        let mut rng = rand::rng();

        let x = rng.random::<u64>() >> 25;

        b.iter(|| {
            let _length = uint_bit_order(&x);
        });
    }

    #[bench]
    fn bench_binary_search(b: &mut Bencher) {
        let mut rng = rand::rng();

        let elem: u64 = rng.random();
        let mut arr: Vec<u64> = (0..1_000_000).map(|_| rng.random()).collect();
        arr.sort();

        b.iter(|| {
            let _idx = binary_search(arr.len(), |i| elem > arr[i]);
        });
    }
}
