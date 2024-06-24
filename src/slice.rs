use core::mem;

use cfg_if::cfg_if;

use super::{Util, Varint};

macro_rules! const_assert {
    ($($tt:tt)+) => {
        const _: () = assert!($($tt)+);
    };
}

/// A slice of [`Varint`][super::int::Varint]s.
pub trait Slice {
    /// Returns the number of bytes needed to encode the
    /// integers.
    fn encoded_len(&self) -> usize;
}

macro_rules! impl_slice_x8 {
    ($name:ty) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let n = (self.len() / 32) * 32;
                let mut sum = n;
                for x in *self {
                    sum += x.to_unsigned().encoded_len();
                }
                sum
            }
        }
    };
}
impl_slice_x8!(u8);
impl_slice_x8!(i8);

macro_rules! impl_slice_x16 {
    ($name:ty) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let n = (self.len() / 32) * 32;
                let mut sum = n;
                let mut iter = self.iter();
                // LLVM autovectorizes this loop.
                for &x in (&mut iter).take(n) {
                    let x: u16 = x.to_unsigned();
                    if x > 0x7F {
                        sum += 1;
                    }
                    if x > 0x3FFF {
                        sum += 1;
                    }
                }
                for x in iter {
                    sum += x.encoded_len();
                }
                sum
            }
        }
    };
}
impl_slice_x16!(u16);
impl_slice_x16!(i16);

macro_rules! impl_slice_x32 {
    ($name:ty) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let n = (self.len() / 32) * 32;
                let mut sum = n;
                let mut iter = self.iter();
                // LLVM autovectorizes this loop.
                for &x in (&mut iter).take(n) {
                    let x: u32 = x.to_unsigned();
                    if x > 0x7F {
                        sum += 1;
                    }
                    if x > 0x3FFF {
                        sum += 1;
                    }
                    if x > 0x1FFFFF {
                        sum += 1;
                    }
                    if x > 0xFFFFFFF {
                        sum += 1;
                    }
                }
                for x in iter {
                    sum += x.encoded_len();
                }
                sum
            }
        }
    };
}
impl_slice_x32!(u32);
impl_slice_x32!(i32);

macro_rules! impl_slice_x64 {
    ($name:ty) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let n = (self.len() / 32) * 32;
                let mut sum = n;
                let mut iter = self.iter();
                // LLVM autovectorizes this loop.
                for &x in (&mut iter).take(n) {
                    let mut x: u64 = x.to_unsigned();
                    let tmp = if x > 1 << 35 { u64::MAX } else { 0 };
                    sum += (5 & tmp) as usize;
                    x >>= 35 & tmp;
                    if x > 0x7F {
                        sum += 1;
                    }
                    if x > 0x3FFF {
                        sum += 1;
                    }
                    if x > 0x1FFFFF {
                        sum += 1;
                    }
                    if x > 0xFFFFFFF {
                        sum += 1;
                    }
                }
                for x in iter {
                    sum += x.encoded_len();
                }
                sum
            }
        }
    };
}
impl_slice_x64!(u64);
impl_slice_x64!(i64);

unsafe trait Xsize {
    type Alias;
}
cfg_if! {
    if #[cfg(target_pointer_width = "64")] {
        unsafe impl Xsize for usize {
            type Alias = u64;
        }
        unsafe impl Xsize for isize {
            type Alias = i64;
        }
    } else if #[cfg(target_pointer_width = "32")] {
        unsafe impl Xsize for usize {
            type Alias = u32;
        }
        unsafe impl Xsize for isize {
            type Alias = i32;
        }
    } else if #[cfg(target_pointer_width = "16")] {
        unsafe impl Xsize for usize {
            type Alias = u16;
        }
        unsafe impl Xsize for isize {
            type Alias = i16;
        }
    } else {
        compile_error!("unreachable")
    }
}
const_assert!(mem::size_of::<usize>() == mem::size_of::<<usize as Xsize>::Alias>(),);
const_assert!(mem::size_of::<isize>() == mem::size_of::<<isize as Xsize>::Alias>(),);

macro_rules! impl_slice_xsize {
    ($name:ty) => {
        impl_slice_xsize!($name, identity);
    };
    ($name:ty, $f:expr) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                // SAFETY: `$name` and
                // same memory layout.
                let data =
                    unsafe { &*(*self as *const [$name] as *const [<$name as Xsize>::Alias]) };
                data.encoded_len()
            }
        }
    };
}
impl_slice_xsize!(usize);
impl_slice_xsize!(isize, Signed::zigzag);

macro_rules! impl_vec {
    ($($ty:ty),+ $(,)?) => {
        $(
            #[cfg(feature = "alloc")]
            impl Slice for ::alloc::vec::Vec<$ty> {
                fn encoded_len(&self) -> usize {
                    self.as_slice().encoded_len()
                }
            }
        )+
    }
}
// TODO: u128/i128
impl_vec! {
    u8, u16, u32, u64, usize,
    i8, i16, i32, i64, isize,
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use super::*;

    macro_rules! test_encoded_len {
        ($name:ident, $ty:ty) => {
            #[test]
            fn $name() {
                fn encoded_len(data: &[$ty]) -> usize {
                    let mut n = 0;
                    for x in data {
                        n += x.encoded_len();
                    }
                    n
                }
                let data = (0..100_000).map(|_| random()).collect::<Vec<$ty>>();
                let got = data.encoded_len();
                let want = encoded_len(&data);
                assert_eq!(got, want);
            }
        };
    }
    test_encoded_len!(test_encoded_len_usize, usize);
    test_encoded_len!(test_encoded_len_isize, isize);
    test_encoded_len!(test_encoded_len_u64, u64);
    test_encoded_len!(test_encoded_len_i64, i64);
    test_encoded_len!(test_encoded_len_u32, u32);
    test_encoded_len!(test_encoded_len_i32, i32);
    test_encoded_len!(test_encoded_len_u16, u16);
    test_encoded_len!(test_encoded_len_i16, i16);
    test_encoded_len!(test_encoded_len_u8, u8);
    test_encoded_len!(test_encoded_len_i8, i8);
}
