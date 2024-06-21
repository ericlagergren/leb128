use core::convert::identity;

use cfg_if::cfg_if;

use super::{Sealed, Signed};

/// A slice of [`Integer`][super::int::Integer]s.
pub trait Slice {
    /// Returns the number of bytes needed to encode the
    /// integers.
    fn encoded_len(&self) -> usize;
}

macro_rules! check_usize {
    ($ty:ty) => {
        const _: () = assert!(::core::mem::size_of::<usize>() == ::core::mem::size_of::<$ty>(),);
    };
}

macro_rules! impl_slice_xsize {
    ($name:ty) => {
        impl_slice_xsize!($name, identity);
    };
    ($name:ty, $f:expr) => {
        #[cfg(any(
            target_pointer_width = "64",
            target_pointer_width = "32",
            target_pointer_width = "16",
        ))]
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let data = {
                    cfg_if! {
                        if #[cfg(target_pointer_width = "64")] {
                            check_usize!(u64);
                            // SAFETY: `usize` and `u64` have the
                            // same memory layout.
                            unsafe {
                                &*(*self as *const [$name] as *const [u64])
                            }
                        } else if #[cfg(target_pointer_width = "32")] {
                            check_usize!(u32);
                            // SAFETY: `usize` and `u32` have the
                            // same memory layout.
                            unsafe {
                                &*(*self as *const [$name] as *const [u32])
                            }
                        } else if #[cfg(target_pointer_width = "16")] {
                            check_usize!(u16);
                            // SAFETY: `usize` and `16` have the
                            // same memory layout.
                            unsafe {
                                &*(*self as *const [$name] as *const [u16])
                            }
                        } else {
                            compile_error!("unreachable")
                        }
                    }
                };
                data.encoded_len()
            }
        }

        #[cfg(all(
            feature = "alloc",
            any(
                target_pointer_width = "64",
                target_pointer_width = "32",
                target_pointer_width = "16",
            )
        ))]
        impl Slice for ::alloc::vec::Vec<$name> {
            fn encoded_len(&self) -> usize {
                self.as_slice().encoded_len()
            }
        }
    };
}
impl_slice_xsize!(usize);
impl_slice_xsize!(isize, Signed::zigzag);

macro_rules! impl_slice_x64 {
    ($name:ty) => {
        impl_slice_x64!($name, identity);
    };
    ($name:ty, $f:expr) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let n = (self.len() / 32) * 32;
                let mut sum = n;
                let mut iter = self.iter();
                // LLVM autovectorizes this loop.
                for &x in (&mut iter).take(n) {
                    let mut x: u64 = $f(x);
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

        #[cfg(feature = "alloc")]
        impl Slice for ::alloc::vec::Vec<$name> {
            fn encoded_len(&self) -> usize {
                self.as_slice().encoded_len()
            }
        }
    };
}
impl_slice_x64!(u64);
impl_slice_x64!(i64, Signed::zigzag);

macro_rules! impl_slice_x32 {
    ($name:ty) => {
        impl_slice_x32!($name, identity);
    };
    ($name:ty, $f:expr) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let n = (self.len() / 32) * 32;
                let mut sum = n;
                let mut iter = self.iter();
                // LLVM autovectorizes this loop.
                for &x in (&mut iter).take(n) {
                    let x: u32 = $f(x);
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

        #[cfg(feature = "alloc")]
        impl Slice for ::alloc::vec::Vec<$name> {
            fn encoded_len(&self) -> usize {
                self.as_slice().encoded_len()
            }
        }
    };
}
impl_slice_x32!(u32);
impl_slice_x32!(i32, Signed::zigzag);

macro_rules! impl_slice_x16 {
    ($name:ty) => {
        impl_slice_x16!($name, identity);
    };
    ($name:ty, $f:expr) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let n = (self.len() / 32) * 32;
                let mut sum = n;
                let mut iter = self.iter();
                // LLVM autovectorizes this loop.
                for &x in (&mut iter).take(n) {
                    let x: u16 = $f(x);
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

        #[cfg(feature = "alloc")]
        impl Slice for ::alloc::vec::Vec<$name> {
            fn encoded_len(&self) -> usize {
                self.as_slice().encoded_len()
            }
        }
    };
}
impl_slice_x16!(u16);
impl_slice_x16!(i16, Signed::zigzag);

macro_rules! impl_slice_x8 {
    ($name:ty) => {
        impl_slice_x8!($name, identity);
    };
    ($name:ty, $f:expr) => {
        impl Slice for &[$name] {
            fn encoded_len(&self) -> usize {
                let n = (self.len() / 32) * 32;
                let mut sum = n;
                let mut iter = self.iter();
                // LLVM autovectorizes this loop.
                for &x in (&mut iter).take(n) {
                    let x: u8 = $f(x);
                    if x > 0x7F {
                        sum += 1;
                    }
                }
                for x in iter {
                    sum += x.encoded_len();
                }
                sum
            }
        }

        #[cfg(feature = "alloc")]
        impl Slice for ::alloc::vec::Vec<$name> {
            fn encoded_len(&self) -> usize {
                self.as_slice().encoded_len()
            }
        }
    };
}
impl_slice_x8!(u8);
impl_slice_x8!(i8, Signed::zigzag);

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
