//! Basic multi precision operations.
//!
//! List of operations:
//! * Addition
//! * Subtraction
//! * Multiplication
//! * Euclidean division ([divide](crate::bigi::Bigi::divide))
//! * Remainder
//! * Overflowing addition ([add_overflowing](crate::bigi::Bigi::add_overflowing))
//! * Overflowing subtraction ([sub_overflowing](crate::bigi::Bigi::sub_overflowing))
//! * Overflowing multiplication ([mul_overflowing](crate::bigi::Bigi::mul_overflowing))
//! * Overflowing euclidean division ([divide_overflowing](crate::bigi::Bigi::divide_overflowing))
//! * Addition with `u64` ([add_unit](crate::bigi::Bigi::add_unit))
//! * Subtraction with `u64` ([sub_unit](crate::bigi::Bigi::sub_unit))
//! * Multiplication with `u64` ([mul_unit](crate::bigi::Bigi::mul_unit))
//! * Division with `u64` ([divide_unit](crate::bigi::Bigi::divide_unit))
//! * Remainder for `2^k` divisor ([rem_2k](crate::bigi::Bigi::rem_2k))
//! * Random generating
//! * Comparison (unsigned)
//! * Bitwise AND
//! * Bitwise OR
//! * Bitwise NOT (`~` or assigned NOT as [bitwise_not_assign](crate::bigi::Bigi::bitwise_not_assign))
//! * Bitwise XOR
//! * Bitwise SHL
//! * Bitwise SHR
//! * Overflowing XOR multiplication ([xor_mul_overflowing](crate::bigi::Bigi::xor_mul_overflowing))
//! * Overflowing XOR division ([xor_divide_overflowing](crate::bigi::Bigi::xor_divide_overflowing))
//!
//! Most of the operations support the assigned interface (`+=`, `-=`, etc).

use std::{cmp, ops, iter};

use rand::prelude::*;
use rand::distr::{Distribution, StandardUniform};

use crate::bigi::{Bigi, BIGI_UNIT_BITS};
use crate::utils::uint_merge;


impl<const N: usize> Bigi<N> {
    /// Division algorithm. The function returns option of the result and `None`
    /// in case of division by zero, `self` turns to the reminder.
    pub fn divide(&mut self, rhs: &Self) -> Option<Self> {
        // Result of division
        let mut div = Self::min();

        // Order of divisor
        let order_rhs = rhs._get_order();

        // Return `None` if divizion by zero
        if order_rhs == 0 {
            return None;
        }

        // Perform `divide_unit` if the order of `rhs` is 1
        if order_rhs == 1 {
            let rem;
            (div, rem) = self.divide_unit(rhs.0[0]).unwrap();
            *self = Self::from(rem);
            return Some(div);
        }

        /*
        Main idea:

            self = 0 ... 0 e a1 b2 ...
            rhs  = 0 ... 0 0 b1 b2 ...

            Way 1: e > 0 (note: e <= b1 otherwise it should be reduced 
                          on the previous step)
                factor = (e|a1) / (b1 + 1)

            Way 2: e == 0
                Case 1: a1 > b1
                    factor = (a1|a2) / ((b1|b2) + 1)

                Case 2: a1 == b1
                    factor = ((a1|a2|...) >= (b1|b2|...)) as integer

                Case 3: a1 < b1
                    factor = 0

            e  = self.0[idx]
            a1 = self.0[idx - 1]
            a2 = self.0[idx - 2]
            b1 =  rhs.0[idx - 1]
            b2 =  rhs.0[idx - 2]
        */

        let mut idx = self._get_order();

        let bottom1 = (rhs.0[order_rhs - 1] as u128) + 1;
        let bottom2 = uint_merge::<_, u128>(
            rhs.0[order_rhs - 1], rhs.0[order_rhs - 2]
        ) + 1;

        while idx >= order_rhs {
            // Define offset
            let offset = idx - order_rhs;

            // Calculate factor
            let factor = {
                // Way 1: e > 0
                if (idx < N) && (self.0[idx] > 0) {
                    (uint_merge::<_, u128>(
                        self.0[idx], self.0[idx - 1]
                    ) / bottom1) as u64
                } 
                // Way 2: e == 0
                else {
                    // Case 1: a1 > b1
                    if self.0[idx - 1] > rhs.0[order_rhs - 1] {
                        (uint_merge::<_, u128>(
                            self.0[idx - 1], self.0[idx - 2]
                        ) / bottom2) as u64
                    }
                    // Case 2: a1 == b1 
                    else if self.0[idx - 1] == rhs.0[order_rhs - 1] {
                        let mut res = 1;
                        for i in (0..(order_rhs - 1)).rev() {
                            if self.0[offset + i] > rhs.0[i] {
                                res = 1;
                                break;
                            }
                            if self.0[offset + i] < rhs.0[i] {
                                res = 0;
                                break;
                            }
                        }
                        res
                    }
                    // Case 3: a1 < b1 
                    else {
                        0
                    }
                }
            };

            if factor > 0 {
                // Increment the result
                div.0[offset] += factor;

                // Reduce `self`
                self._sub_offset(rhs, offset, factor);
            } else {
                // Decrement `idx`
                idx -= 1;
            }
        }

        Some(div)
    }

    /// Multiplication algorithm with overflowing part. The function returns
    /// a pair result-overflow.
    pub fn mul_overflowing(&self, rhs: &Self) -> (Self, Self) {
        let mut res = Bigi::<N>::min();
        let mut ext = Bigi::<N>::min();

        let order_rhs = rhs._get_order();

        for i_rhs in 0..order_rhs {
            let mut carry: u64 = 0;
            let mut overflow = false;

            for i_self in 0..N {
                let i_res = i_rhs + i_self;

                if i_res < N {
                    (carry, overflow) = carry.carrying_add(res.0[i_res], overflow);
                    (res.0[i_res], carry) = self.0[i_self].carrying_mul(rhs.0[i_rhs], carry);
                } else {
                    (carry, overflow) = carry.carrying_add(ext.0[i_res - N], overflow);
                    (ext.0[i_res - N], carry) = self.0[i_self].carrying_mul(rhs.0[i_rhs], carry);
                }
            }

            for i_ext in i_rhs..N {
                (ext.0[i_ext], overflow) = ext.0[i_ext].carrying_add(carry, overflow);
                carry = 0;

                if !overflow {
                    break;
                }
            }
        }

        (res, ext)
    }

    /// Same as `divide` but the divible includes overflowing part `ext`.
    /// After execution `ext` turns to 0.
    pub fn divide_overflowing(&mut self, rhs: &Self, ext: &mut Self) -> Option<Self> {
        // Set `idx` in the loop below to the size considering overflow
        let mut idx = ext._get_order() + N;

        // Perform plain `divide` if overflowing part is zero
        if idx <= N {
            return self.divide(rhs);
        }

        // Result of division
        let mut div = Self::min();

        // Order of divisor
        let order_rhs = rhs._get_order();

        // Return `None` if divizion by zero
        if order_rhs == 0 {
            return None;
        }

        // Perform `divide_unit` if the order of `rhs` is 1
        if order_rhs == 1 {
            let rem;
            (div, rem) = self.divide_unit(rhs.0[0]).unwrap();
            *self = Self::from(rem);
            return Some(div);
        }

        /*
        Main idea:

            self = 0 ... 0 e a1 b2 ...
            rhs  = 0 ... 0 0 b1 b2 ...

            Way 1: e > 0 (note: e <= b1 otherwise it should be reduced 
                          on the previous step)
                factor = (e|a1) / (b1 + 1)

            Way 2: e == 0
                Case 1: a1 > b1
                    factor = (a1|a2) / ((b1|b2) + 1)

                Case 2: a1 == b1
                    factor = ((a1|a2|...) >= (b1|b2|...)) as integer

                Case 3: a1 < b1
                    factor = 0

            e  = self.0[idx]
            a1 = self.0[idx - 1]
            a2 = self.0[idx - 2]
            b1 =  rhs.0[idx - 1]
            b2 =  rhs.0[idx - 2]
        */

        let bottom1 = (rhs.0[order_rhs - 1] as u128) + 1;
        let bottom2 = uint_merge::<_, u128>(
            rhs.0[order_rhs - 1], rhs.0[order_rhs - 2]
        ) + 1;

        while idx >= order_rhs {
            // Define offset
            let offset = idx - order_rhs;

            // Calculate factor
            let factor = {
                let is_way1 = if idx < N {
                    self.0[idx] > 0
                } else if idx < 2 * N {
                    ext.0[idx - N] > 0
                } else {
                    false
                };

                // Way 1: e > 0
                if is_way1 {
                    // Pair (e, a1)
                    let pair = if idx < N {
                        (self.0[idx], self.0[idx - 1])
                    } else if idx == N {
                        (ext.0[0], self.0[N - 1])
                    } else {
                        (ext.0[idx - N], ext.0[idx - N - 1])
                    };

                    (uint_merge::<_, u128>(pair.0, pair.1) / bottom1) as u64
                } 
                // Way 2: e == 0
                else {
                    // Pair (a1, a2)
                    let pair = if idx < (N + 1) {
                        (self.0[idx - 1], self.0[idx - 2])
                    } else if idx == (N + 1) {
                        (ext.0[0], self.0[N - 1])
                    } else {
                        (ext.0[idx - N - 1], ext.0[idx - N - 2])
                    };

                    // Case 1: a1 > b1
                    if pair.0 > rhs.0[order_rhs - 1] {
                        (uint_merge::<_, u128>(pair.0, pair.1) / bottom2) as u64
                    }
                    // Case 2: a1 == b1 
                    else if pair.0 == rhs.0[order_rhs - 1] {
                        let mut res = None;

                        for i in (0 .. order_rhs - 1).rev() {
                            let val = if offset + i < N {
                                self.0[offset + i]
                            } else {
                                ext.0[offset + i - N]
                            };
                            if val > rhs.0[i] {
                                res = Some(1);
                                break;
                            }
                            if val < rhs.0[i] {
                                res = Some(0);
                                break;
                            }
                        }

                        res.unwrap_or(1)
                    }
                    // Case 3: a1 < b1 
                    else {
                        0
                    }
                }
            };

            if factor > 0 {
                // Increment the result
                div.0[offset] += factor;

                // Reduce `self` and `ext`
                let mut carry = 0;
                let mut overflow = false;
                let mut tmp;
                for i in offset..N {
                    (tmp, carry) = rhs.0[i - offset].carrying_mul(factor, carry);
                    (self.0[i], overflow) = self.0[i].borrowing_sub(tmp, overflow);
                }
                for i in 0..offset {
                    (tmp, carry) = rhs.0[i + N - offset].carrying_mul(factor, carry);
                    (ext.0[i], overflow) = ext.0[i].borrowing_sub(tmp, overflow);
                }
                for i in offset..N {
                    (ext.0[i], overflow) = ext.0[i].borrowing_sub(carry, overflow);
                    carry = 0;
                    if !overflow {
                        break;
                    }
                }
            } else {
                // Decrement `idx`
                idx -= 1;
            }
        }

        Some(div)
    }

    /// Assigned addition with overflowing. It returns `true` if overflowing
    /// happened.
    pub fn add_overflowing(&mut self, rhs: &Self) -> bool {
        self._add_offset(rhs, 0, 1) > 0
    }

    /// Assigned subtraction with overflowing. It returns `true` if overflowing
    /// happened.
    pub fn sub_overflowing(&mut self, rhs: &Self) -> bool {
        self._sub_offset(rhs, 0, 1) > 0
    }

    fn _add_offset(&mut self, rhs: &Self, offset: usize, factor: u64) -> u64 {
        let mut carry = 0;
        let mut overflow = false;
        let mut tmp;
        for idx in offset..N {
            (tmp, carry) = rhs.0[idx - offset].carrying_mul(factor, carry);
            (self.0[idx], overflow) = self.0[idx].carrying_add(tmp, overflow);
        }
        if overflow {
            carry += 1
        }
        carry
    }

    fn _sub_offset(&mut self, rhs: &Self, offset: usize, factor: u64) -> u64 {
        let mut carry = 0;
        let mut overflow = false;
        let mut tmp;
        for idx in offset..N {
            (tmp, carry) = rhs.0[idx - offset].carrying_mul(factor, carry);
            (self.0[idx], overflow) = self.0[idx].borrowing_sub(tmp, overflow);
        }
        if overflow {
            carry += 1
        }
        carry
    }

    fn _xor_offset(&mut self, rhs: &Self, offset: isize) {
        // Split `offset`
        let q: isize = offset.div_euclid(BIGI_UNIT_BITS as isize);
        let r: usize = offset.rem_euclid(BIGI_UNIT_BITS as isize) as usize;

        // Clamp iterator betweeb max(a1, a2) and min(b1, b2)
        let clamp = |(a1, a2), (b1, b2)| {
            std::cmp::max::<isize>(a1, a2)
            ..
            std::cmp::min::<isize>(b1, b2)
        };

        // Right part of `rhs` digit
        for i in clamp((0, -q), (N as isize, N as isize - q)) {
            self.0[(i + q) as usize] ^= rhs.0[i as usize] << r;
        }

        // Left part of `rhs` digit
        if r > 0 {
            for i in clamp((0, -q - 1), (N as isize, N as isize - q - 1)) {
                self.0[(i + q + 1) as usize] ^= 
                    rhs.0[i as usize] >> (BIGI_UNIT_BITS - r);
            }
        }
    }

    /// Assigned addition (increment) with a plain `u64` integer.
    /// It returns `true` if overflowing happened.
    pub fn add_unit(&mut self, unit: u64) -> bool {
        let mut carry;
        (self.0[0], carry) = self.0[0].overflowing_add(unit);
        if carry {
            for idx in 1..N {
                (self.0[idx], carry) = self.0[idx].carrying_add(0, carry);
                if !carry {
                    break;
                }
            }
        }
        carry
    }

    /// Assigned subtraction (decrement) with a plain `u64` integer.
    /// It returns `true` if overflowing happened.
    pub fn sub_unit(&mut self, unit: u64) -> bool {
        let mut carry;
        (self.0[0], carry) = self.0[0].overflowing_sub(unit);
        if carry {
            for idx in 1..N {
                (self.0[idx], carry) = self.0[idx].borrowing_sub(0, carry);
                if !carry {
                    break;
                }
            }
        }
        carry
    }

    /// Assigned multiplication with a plain `u64` integer.
    /// It returns the overflowing integer.
    pub fn mul_unit(&mut self, unit: u64) -> u64 {
        let mut carry = 0;
        for idx in 0..N {
            (self.0[idx], carry) = self.0[idx].carrying_mul(unit, carry);
        }
        carry
    }

    /// Division by a plain `u64` integer. The function returns an option
    /// of pair result-reminder or `None` in case of zero divisor.
    pub fn divide_unit(&self, unit: u64) -> Option<(Self, u64)> {
        if unit > 0 {
            let unit2 = unit as u128;
            let mut res = [0; N];
            let mut lead = 0;
            for idx in (0..N).rev() {
                lead <<= BIGI_UNIT_BITS;
                lead |= self.0[idx] as u128;
                res[idx] = (lead / unit2) as u64;
                lead %= unit2;
            }
            Some((Self::new(res), lead as u64))
        } else {
            None
        }
    }

    /// Bitwise not.
    pub fn bitwise_not_assign(&mut self) {
        for digit in self.0.iter_mut() {
            *digit = !*digit;
        }
    }

    /// Leaves last `k` bits of the integers, others are turned to zero.
    /// It is equal to taking reminder from division by `2^k`.
    pub fn rem_2k(&mut self, k: usize) {
        let (q, r) = Self::_bit_split_index(k);

        if q < N {
            self.0[q] &= if r > 0 {
                u64::MAX >> (BIGI_UNIT_BITS - r)
            } else {
                0
            };
        }

        for idx in (q + 1)..N {
            self.0[idx] = 0;
        }
    }

    /// Performs XOR multiplication with overflowing. It keeps 
    /// the distributive property regarding XOR as an addition operation: 
    /// `(a * b) ^ (a * c) = a * (b ^ c)`
    pub fn xor_mul_overflowing(&self, rhs: &Self) -> (Self, Self) {
        let mut res = Self::min();
        let mut ext = Self::min();
        for (offset, bit) in self.bit_iter().enumerate() {
            if bit {
                res._xor_offset(rhs, offset as isize);
                ext._xor_offset(
                    rhs, offset as isize - (N * BIGI_UNIT_BITS) as isize
                );
            }
        }
        (res, ext)
    }

    /// Performs XOR division with overflowing as the inversion for 
    /// the multiplication.
    pub fn xor_divide_overflowing(&mut self, rhs: &Self, ext: &mut Self) -> 
            Option<Self> {
        let order_rhs = rhs.bit_len();
        let order_ext = ext.bit_len();

        let mut order_self = if order_ext == 0 {
            self.bit_len()
        } else {
            N * BIGI_UNIT_BITS + order_ext
        };

        if order_rhs > 0 {
            let mut res = Self::min();

            while order_self >= order_rhs {
                let bit = if order_self <= N * BIGI_UNIT_BITS {
                    self.bit_get(order_self - 1)
                } else {
                    ext.bit_get(order_self - 1 - N * BIGI_UNIT_BITS)
                };

                if bit {
                    let offset = order_self - order_rhs;

                    self._xor_offset(rhs, offset as isize);
                    ext._xor_offset(
                        rhs, offset as isize - (N * BIGI_UNIT_BITS) as isize
                    );

                    res.bit_set(offset, true);
                }
                order_self -= 1;
            }

            Some(res)
        } else {
            None
        }
    }
}


impl<const N: usize> Distribution<Bigi<N>> for StandardUniform {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Bigi<N> {
        Bigi::<N>::from_iter(
            (0..N).map(|_| rng.random())
        )
    }
}


impl<const N: usize> PartialOrd for Bigi<N> {
    fn partial_cmp(&self, rhs: &Bigi<N>) -> Option<cmp::Ordering> {
        for idx in (0..N).rev() {
            if self.0[idx] < rhs.0[idx] {
                return Some(cmp::Ordering::Less);
            }
            if self.0[idx] > rhs.0[idx] {
                return Some(cmp::Ordering::Greater);
            }
        }
        Some(cmp::Ordering::Equal)
    }
}


impl<const N: usize> Ord for Bigi<N> {
    fn cmp(&self, rhs: &Bigi<N>) -> cmp::Ordering {
        self.partial_cmp(rhs).unwrap()
    }
}


impl<const N: usize> ops::Not for &Bigi<N> {
    type Output = Bigi<N>;

    fn not(self) -> Bigi<N> {
        let mut res = self.clone();
        res.bitwise_not_assign();
        res
    }
}


impl<const N: usize> ops::BitAndAssign<&Bigi<N>> for Bigi<N> {
    fn bitand_assign(&mut self, rhs: &Bigi<N>) {
        for idx in 0..N {
            self.0[idx] &= rhs.0[idx];
        }
    }
}


impl<const N: usize> ops::BitOrAssign<&Bigi<N>> for Bigi<N> {
    fn bitor_assign(&mut self, rhs: &Bigi<N>) {
        for idx in 0..N {
            self.0[idx] |= rhs.0[idx];
        }
    }
}


impl<const N: usize> ops::BitXorAssign<&Bigi<N>> for Bigi<N> {
    fn bitxor_assign(&mut self, rhs: &Bigi<N>) {
        for idx in 0..N {
            self.0[idx] ^= rhs.0[idx];
        }
    }
}


impl<const N: usize> ops::BitAnd<&Bigi<N>> for &Bigi<N> {
    type Output = Bigi<N>;

    fn bitand(self, rhs: &Bigi<N>) -> Bigi<N> {
        let mut res = self.clone();
        res &= rhs;
        res
    }
}


impl<const N: usize> ops::BitOr<&Bigi<N>> for &Bigi<N> {
    type Output = Bigi<N>;

    fn bitor(self, rhs: &Bigi<N>) -> Bigi<N> {
        let mut res = self.clone();
        res |= rhs;
        res
    }
}


impl<const N: usize> ops::BitXor<&Bigi<N>> for &Bigi<N> {
    type Output = Bigi<N>;

    fn bitxor(self, rhs: &Bigi<N>) -> Bigi<N> {
        let mut res = self.clone();
        res ^= rhs;
        res
    }
}


impl<const N: usize> ops::AddAssign<&Bigi<N>> for Bigi<N> {
    fn add_assign(&mut self, rhs: &Bigi<N>) {
        self._add_offset(rhs, 0, 1);
    }
}


impl<const N: usize> ops::SubAssign<&Bigi<N>> for Bigi<N> {
    fn sub_assign(&mut self, rhs: &Bigi<N>) {
        self._sub_offset(rhs, 0, 1);
    }
}


impl<const N: usize> ops::MulAssign<u64> for Bigi<N> {
    fn mul_assign(&mut self, rhs: u64) {
        self.mul_unit(rhs);
    }
}


impl<const N: usize> ops::DivAssign<u64> for Bigi<N> {
    fn div_assign(&mut self, rhs: u64) {
        *self = &*self / rhs;
    }
}


impl<const N: usize> ops::MulAssign<&Bigi<N>> for Bigi<N> {
    fn mul_assign(&mut self, rhs: &Bigi<N>) {
        *self = &self.clone() * rhs;
    }
}


impl<const N: usize> ops::DivAssign<&Bigi<N>> for Bigi<N> {
    fn div_assign(&mut self, rhs: &Bigi<N>) {
        *self = &self.clone() / rhs;
    }
}


impl<const N: usize> ops::RemAssign<&Bigi<N>> for Bigi<N> {
    fn rem_assign(&mut self, rhs: &Bigi<N>) {
        self.divide(rhs).expect("Division by zero");
    }
}


impl<const N: usize> ops::Add<&Bigi<N>> for &Bigi<N> {
    type Output = Bigi<N>;

    fn add(self, rhs: &Bigi<N>) -> Bigi<N> {
        let mut res = self.clone();
        res += rhs;
        res
    }
}


impl<const N: usize> ops::Sub<&Bigi<N>> for &Bigi<N> {
    type Output = Bigi<N>;

    fn sub(self, rhs: &Bigi<N>) -> Bigi<N> {
        let mut res = self.clone();
        res -= rhs;
        res
    }
}


impl<const N: usize> ops::Mul<u64> for &Bigi<N> {
    type Output = Bigi<N>;

    fn mul(self, rhs: u64) -> Bigi<N> {
        let mut res = self.clone();
        res *= rhs;
        res
    }
}


impl<const N: usize> ops::Div<u64> for &Bigi<N> {
    type Output = Bigi<N>;

    fn div(self, rhs: u64) -> Bigi<N> {
        self.divide_unit(rhs).expect("Division by zero").0
    }
}


impl<const N: usize> ops::Rem<u64> for &Bigi<N> {
    type Output = u64;

    fn rem(self, rhs: u64) -> u64 {
        self.divide_unit(rhs).expect("Division by zero").1
    }
}


impl<const N: usize> ops::Mul<&Bigi<N>> for &Bigi<N> {
    type Output = Bigi<N>;

    fn mul(self, rhs: &Bigi<N>) -> Bigi<N> {
        let mut res = Bigi::<N>::min();
        for idx in 0..rhs._get_order() {
            res._add_offset(&self, idx, rhs.0[idx]);
        }
        res
    }
}


impl<const N: usize> ops::Div<&Bigi<N>> for &Bigi<N> {
    type Output = Bigi<N>;

    fn div(self, rhs: &Bigi<N>) -> Bigi<N> {
        let mut self_copy = self.clone();
        self_copy.divide(rhs).expect("Division by zero")
    }
}


impl<const N: usize> ops::Rem<&Bigi<N>> for &Bigi<N> {
    type Output = Bigi<N>;

    fn rem(self, rhs: &Bigi<N>) -> Bigi<N> {
        let mut self_copy = self.clone();
        self_copy.divide(rhs).expect("Division by zero");
        self_copy
    }
}


impl<const N: usize> ops::ShrAssign<usize> for Bigi<N> {
    fn shr_assign(&mut self, rhs: usize) {
        let (q, r) = Self::_bit_split_index(rhs);

        if q >= N {
            panic!("Shift with overflow");
        }

        self.0[0] = self.0[q] >> r;

        for idx in 1..(N - q) {
            if r > 0 {
                self.0[idx - 1] |= self.0[idx + q] << (BIGI_UNIT_BITS - r);
            }
            self.0[idx] = self.0[idx + q] >> r;
        }

        for idx in (N - q)..N {
            self.0[idx] = 0;
        }
    }
}


impl<const N: usize> ops::ShlAssign<usize> for Bigi<N> {
    fn shl_assign(&mut self, rhs: usize) {
        let (q, r) = Self::_bit_split_index(rhs);

        if q >= N {
            panic!("Shift with overflow");
        }

        self.0[N - 1] = self.0[N - 1 - q] << r;

        for idx in (q..(N - 1)).rev() {
            if r > 0 {
                self.0[idx + 1] |= self.0[idx - q] >> (BIGI_UNIT_BITS - r);
            }
            self.0[idx] = self.0[idx - q] << r;
        }
        

        for idx in 0..q {
            self.0[idx] = 0;
        }
    }
}


impl<const N: usize> ops::Shr<usize> for &Bigi<N> {
    type Output = Bigi<N>;

    fn shr(self, rhs: usize) -> Bigi<N> {
        let mut self_copy = self.clone();
        self_copy >>= rhs;
        self_copy
    }
}


impl<const N: usize> ops::Shl<usize> for &Bigi<N> {
    type Output = Bigi<N>;

    fn shl(self, rhs: usize) -> Bigi<N> {
        let mut self_copy = self.clone();
        self_copy <<= rhs;
        self_copy
    }
}


impl<const N: usize> iter::Sum for Bigi<N> {
    fn sum<I: Iterator<Item = Bigi<N>>>(it: I) -> Bigi<N> {
        it.fold(Bigi::<N>::from(0), |s, v| &s + &v)
    }
}


impl<'a, const N: usize> iter::Sum<&'a Bigi<N>> for Bigi<N> {
    fn sum<I: Iterator<Item = &'a Bigi<N>>>(it: I) -> Bigi<N> {
        it.fold(Bigi::<N>::from(0), |s, v| &s + v)
    }
}


impl<const N: usize> iter::Product for Bigi<N> {
    fn product<I: Iterator<Item = Bigi<N>>>(it: I) -> Bigi<N> {
        it.fold(Bigi::<N>::from(1), |s, v| &s * &v)
    }
}


impl<'a, const N: usize> iter::Product<&'a Bigi<N>> for Bigi<N> {
    fn product<I: Iterator<Item = &'a Bigi<N>>>(it: I) -> Bigi<N> {
        it.fold(Bigi::<N>::from(1), |s, v| &s * v)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;
    use rand::Rng;

    #[test]
    fn test_not() {
        let a = Bigi::new([25, 48, 1000, 2]);

        let b = !&a;
        assert_eq!(b, Bigi([18446744073709551590, 18446744073709551567, 
                            18446744073709550615, 18446744073709551613]));

        let c = !&b;
        assert_eq!(c, a);
    }

    #[test]
    fn test_add() {
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
        let b = Bigi::<4>::from_decimal(
            "31748292332736638260997326595003206151062806364501393100925672066615273796617"
        );

        let c = &a + &b;
        
        assert_eq!(
            c.to_decimal(), 
            "101759889414982340782287414042809734914479841965229569538455714196276019379844"
        );
    }

    #[test]
    fn test_sub() {
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
        let b = Bigi::<4>::from_decimal(
            "31748292332736638260997326595003206151062806364501393100925672066615273796617"
        );

        let c = &a - &b;
        
        assert_eq!(
            c.to_decimal(), 
            "38263304749509064260292760852803322612354229236226783336604370063045471786610"
        );
    }

    #[test]
    fn test_mul() {
        let a = Bigi::<8>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
        let b = Bigi::<8>::from_decimal(
            "31748292332736638260997326595003206151062806364501393100925672066615273796617"
        );

        let c = &a * &b;
        
        assert_eq!(
            c.to_decimal(), 
            "2222748650848908031820938128993338719537265726594322509944619487708154171020933436409596870357396856024737376838906180914669746523938439158164990244543059"
        );
    }

    #[test]
    fn test_divide() {
        let mut a = Bigi::<8>::from_decimal(
            "2222748650848908031820938128993338719537265726594322509944619487708154171020947637063209347237239307841035167373133790247706897296063852563488002094463544"
        );
        let b = Bigi::<8>::from_decimal(
            "31748292332736638260997326595003206151062806364501393100925672066615273796617"
        );

        let c = a.divide(&b).unwrap();
        
        assert_eq!(
            a.to_decimal(), 
            "14200653612476879842451816297790534227609333037150772125413405323011849920485"
        );
        assert_eq!(
            c.to_decimal(), 
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
    }

    #[test]
    fn test_mul_overflowing() {
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
        let b = Bigi::<4>::from_decimal(
            "31748292332736638260997326595003206151062806364501393100925672066615273796617"
        );

        let (c, d) = a.mul_overflowing(&b);
        
        assert_eq!(
            c.to_decimal(), 
            "83124185284072395376147248273023996569765850980361554076138593327701239126611"
        );
        assert_eq!(
            d.to_decimal(), 
            "19196032004339940264156369392730172788471585046317824464785362576582808626618"
        );
    }

    #[test]
    fn test_divide_overflow() {
        let mut a = Bigi::<4>::from_decimal(
            "97324838896549275218599064570814530797375184017512326201551998650713089047096"
        );
        let mut e = Bigi::<4>::from_decimal(
            "19196032004339940264156369392730172788471585046317824464785362576582808626618"
        );
        let b = Bigi::<4>::from_decimal(
            "31748292332736638260997326595003206151062806364501393100925672066615273796617"
        );

        let c = a.divide_overflowing(&b, &mut e).unwrap();
        
        assert_eq!(
            a.to_decimal(), 
            "14200653612476879842451816297790534227609333037150772125413405323011849920485"
        );
        assert_eq!(
            e.to_decimal(), 
            "0"
        );
        assert_eq!(
            c.to_decimal(), 
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
    }

    #[test]
    fn test_shr() {
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        assert_eq!(
            (&a >> 37).to_decimal(), 
            "509401412871707743916268281811837578159007793879778011160160837823"
        );
        assert_eq!(
            (&a >> 128).to_decimal(), 
            "205745592155564925798070843291128789445"
        );
        assert_eq!(
            (&a >> 165).to_decimal(), 
            "1496996207828960365427125676"
        );
    }

    #[test]
    fn test_shl() {
        let a = Bigi::<4>::from_decimal(
            "1496996207828960365427125676"
        );

        assert_eq!(
            (&a << 37).to_decimal(), 
            "205745592155564925798070843190460547072"
        );
        assert_eq!(
            (&a << 128).to_decimal(), 
            "509401412871707743916268281562595082322371416996491562633454944256"
        );
        assert_eq!(
            (&a << 165).to_decimal(), 
            "70011597082245702521290087413550900974880414885283513864019987874208737656832"
        );
    }

    #[test]
    fn test_rem_2k() {
        let mut a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        a.rem_2k(256);
        assert_eq!(a.to_decimal(), "70011597082245702521290087447806528763417035600728176437530042129660745583227");

        a.rem_2k(103);
        assert_eq!(a.to_decimal(), "2895417069343791920015431142011");

        a.rem_2k(150);
        assert_eq!(a.to_decimal(), "2895417069343791920015431142011");

        a.rem_2k(64);
        assert_eq!(a.to_decimal(), "13052583939777464955");

        a.rem_2k(10);
        assert_eq!(a.to_decimal(), "635");

        a.rem_2k(1);
        assert_eq!(a.to_decimal(), "1");

        a.rem_2k(0);
        assert_eq!(a.to_decimal(), "0");
    }

    #[test]
    fn test_xor_mul_divide() {
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
        let b = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let (mut c, mut e) = a.xor_mul_overflowing(&b);

        assert_eq!(c.to_decimal(), "65309662055680002716446342058602905594080210850251883629534663133943382621715");
        assert_eq!(e.to_decimal(), "45516525973600415825015660741683020399346275692651436656915901048781668865316");

        c ^= &Bigi::from(25);

        let d = c.xor_divide_overflowing(&b, &mut e).unwrap();

        assert_eq!(c, Bigi::from(25));
        assert_eq!(e, Bigi::from(0));
        assert_eq!(d, a);
    }

    #[test]
    fn test_agg() {
        let a = Bigi::<8>::from_decimal(
            "20011597082245702521290087447806528763417035600728176437530042129660745583227"
        );
        let b = Bigi::<8>::from_decimal(
            "19893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let v = vec![a.clone(), b.clone()];
        let s: Bigi<8> = v.iter().sum();
        assert_eq!(s.to_decimal(), "39905344408515605144632876952990256578770479631007693940820868571199207721620");
        let s: Bigi<8> = v.into_iter().sum();
        assert_eq!(s.to_decimal(), "39905344408515605144632876952990256578770479631007693940820868571199207721620");
    
        let v = vec![a.clone(), b.clone()];
        let s: Bigi<8> = v.iter().product();
        assert_eq!(s.to_decimal(), "398105655949316029157683162537840339767936735094699854289612040283448162948749190579803666804624720023677178215273049342981008161873882543482140373534211");
        let s: Bigi<8> = v.into_iter().product();
        assert_eq!(s.to_decimal(), "398105655949316029157683162537840339767936735094699854289612040283448162948749190579803666804624720023677178215273049342981008161873882543482140373534211");
    
        let v = vec![a.clone(), b.clone()];
        let s: &Bigi<8> = v.iter().min().unwrap();
        assert_eq!(s.to_decimal(), "19893747326269902623342789505183727815353444030279517503290826441538462138393");
        let s: Bigi<8> = v.into_iter().min().unwrap();
        assert_eq!(s.to_decimal(), "19893747326269902623342789505183727815353444030279517503290826441538462138393");
    
        let v = vec![a.clone(), b.clone()];
        let s: &Bigi<8> = v.iter().max().unwrap();
        assert_eq!(s.to_decimal(), "20011597082245702521290087447806528763417035600728176437530042129660745583227");
        let s: Bigi<8> = v.into_iter().max().unwrap();
        assert_eq!(s.to_decimal(), "20011597082245702521290087447806528763417035600728176437530042129660745583227");
    }

    #[bench]
    fn bench_clone(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a: Bigi<4> = rng.random();

        bencher.iter(|| {
            let _b = a.clone();
        });
    }

    #[bench]
    fn bench_random_256(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        bencher.iter(|| {
            let _a: Bigi<4> = rng.random();
        });
    }

    #[bench]
    fn bench_not(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a: Bigi<4> = rng.random();

        bencher.iter(|| {
            let _b = !&a;
        });
    }

    #[bench]
    fn bench_bitand(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = rng.random::<Bigi<4>>();
        let b = rng.random::<Bigi<4>>();

        bencher.iter(|| {
            let _c = &a & &b;
        });
    }

    #[bench]
    fn bench_bitor(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = rng.random::<Bigi<4>>();
        let b = rng.random::<Bigi<4>>();

        bencher.iter(|| {
            let _c = &a | &b;
        });
    }

    #[bench]
    fn bench_bitxor(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = rng.random::<Bigi<4>>();
        let b = rng.random::<Bigi<4>>();

        bencher.iter(|| {
            let _c = &a ^ &b;
        });
    }

    #[bench]
    fn bench_add(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = rng.random::<Bigi<4>>();
        let b = rng.random::<Bigi<4>>();

        bencher.iter(|| {
            let _c = &a + &b;
        });
    }

    #[bench]
    fn bench_sub(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = rng.random::<Bigi<4>>();
        let b = rng.random::<Bigi<4>>();

        bencher.iter(|| {
            let _c = &a - &b;
        });
    }

    #[bench]
    fn bench_mul(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = Bigi::<8>::from(&rng.random::<Bigi<4>>());
        let b = Bigi::<8>::from(&rng.random::<Bigi<4>>());

        bencher.iter(|| {
            let _c = &a * &b;
        });
    }

    #[bench]
    fn bench_mul_overflowing(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = rng.random::<Bigi<4>>();
        let b = rng.random::<Bigi<4>>();

        bencher.iter(|| {
            let _c = a.mul_overflowing(&b);
        });
    }

    #[bench]
    fn bench_divide(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = rng.random::<Bigi<8>>();
        let b = Bigi::<8>::from(&rng.random::<Bigi<4>>());

        bencher.iter(|| {
            let _c = &a * &b;
        });
    }

    #[bench]
    fn bench_divide_overflowing(bencher: &mut Bencher) {
        let mut rng = rand::rng();

        let a = rng.random::<Bigi<4>>();
        let b = rng.random::<Bigi<4>>();

        let (m, e) = a.mul_overflowing(&b);

        bencher.iter(|| {
            let mut m_mut = m.clone();
            let mut e_mut = e.clone();
            let _c = m_mut.divide_overflowing(&b, &mut e_mut);
        });
    }

    #[bench]
    fn bench_rem_2k(bencher: &mut Bencher) {
        // Arbitrary number
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        bencher.iter(|| {
            let mut b = a.clone();
            b.rem_2k(103);
        });
    }
}
