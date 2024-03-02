use crate::bigi::{Bigi, BIGI_UNIT_BITS};


impl<const N: usize, const M: usize> From<&Bigi<N>> for Bigi<M> {
    fn from(a: &Bigi<N>) -> Self {
        let mut arr = [0; M];
        if N >= M {
            arr.clone_from_slice(&a.0[..M]);
        } else {
            arr[..N].clone_from_slice(&a.0);
        }
        Self(arr)
    }
}


impl<const N: usize> From<u64> for Bigi<N> {
    fn from(x: u64) -> Self {
        let mut arr = [0; N];
        arr[0] = x;
        Self(arr)
    }
}


impl<const N: usize> From<&Bigi<N>> for u64 {
    fn from(a: &Bigi<N>) -> u64 {
        a.0[0]
    }
}


impl<const N: usize> From<u128> for Bigi<N> {
    fn from(x: u128) -> Self {
        let mut arr = [0; N];
        arr[0] = x as u64;
        arr[1] = (x >> BIGI_UNIT_BITS) as u64;
        Self(arr)
    }
}


impl<const N: usize> From<&Bigi<N>> for u128 {
    fn from(a: &Bigi<N>) -> u128 {
        ((a.0[1] as u128) << BIGI_UNIT_BITS) | (a.0[0] as u128)
    }
}


macro_rules! define_convert_from_integer {
    ($type:ident) => {
        impl<const N: usize> From<$type> for Bigi<N> {
            fn from(x: $type) -> Self {
                Self::from(x as u64)
            }
        }
    };
}


define_convert_from_integer!(i8);
define_convert_from_integer!(i16);
define_convert_from_integer!(i32);
define_convert_from_integer!(i64);
define_convert_from_integer!(u8);
define_convert_from_integer!(u16);
define_convert_from_integer!(u32);
define_convert_from_integer!(usize);
define_convert_from_integer!(bool);


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u64() {
        let a = Bigi::<4>::from(25);
        assert_eq!(a, Bigi::new([25, 0, 0, 0]));

        let x = u64::from(&a);
        assert_eq!(x, 25);
    }

    #[test]
    fn test_u128() {
        let a = Bigi::new([25, 48, 1000, 2]);

        let x = u128::from(&a);
        assert_eq!(x, 885443715538058477593);

        let b = Bigi::<4>::from(x);
        assert_eq!(b, Bigi::new([25, 48, 0, 0]));
    }

    #[test]
    fn test_bigi() {
        let a = Bigi::new([25, 48, 1000, 2]);

        let b = Bigi::<2>::from(&a);
        assert_eq!(b, Bigi::new([25, 48]));

        let c = Bigi::<4>::from(&b);
        assert_eq!(c, Bigi::new([25, 48, 0, 0]));
    }
}
