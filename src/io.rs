#![cfg(feature = "std")]
#![cfg_attr(docsrs, doc(cfg(feature = "std")))]

use std::io::{Bytes, Error, Read, Result, Write};

use super::{Overflow, Varint};

macro_rules! write_impl {
    ($type:ty, $name:ident) => {
        #[doc = "Writes a LEB128-encoded `"]
        #[doc = stringify!($type)]
        #[doc = "` and returns the number of bytes written."]
        fn $name(&mut self, x: $type) -> Result<usize> {
            self.write_int(x)
        }
    };
}

/// Extends [`Write`] with methods for reading LEB128-encoded
/// integers.
pub trait WriteVarint: Write {
    /// Writes a LEB128-encoded integer and returns the number of
    /// bytes written.
    fn write_int<T: Varint>(&mut self, x: T) -> Result<usize> {
        let mut buf = T::Buf::default();
        let encoded = x.write(&mut buf);
        self.write_all(encoded)?;
        Ok(encoded.len())
    }

    write_impl!(u8, write_u8);
    write_impl!(u16, write_u16);
    write_impl!(u32, write_u32);
    write_impl!(u64, write_u64);
    write_impl!(u128, write_u128);
    write_impl!(usize, write_usize);

    write_impl!(i8, write_i8);
    write_impl!(i16, write_i16);
    write_impl!(i32, write_i32);
    write_impl!(i64, write_i64);
    write_impl!(i128, write_i128);
    write_impl!(isize, write_isize);
}

macro_rules! read_impl {
    ($type:ty, $name:ident) => {
        #[doc = "Reads a LEB128-encoded `"]
        #[doc = stringify!($type)]
        #[doc = "`."]
        fn $name(&mut self) -> Result<$type> {
            self.read_int()
        }
    };
}

impl<W: Write + ?Sized> WriteVarint for W {}

/// Extends [`Read`] with methods for reading LEB128-encoded
/// integers.
pub trait ReadVarintExt: Read {
    /// Reads a LEB128-encoded integer.
    fn read_int<T: Varint>(&mut self) -> Result<T> {
        let mut iter = Iter::new(self.bytes());
        let (v, _) = T::read_iter(&mut iter).map_err(Error::other)?;
        if let Some(err) = iter.err {
            Err(err)
        } else {
            Ok(v)
        }
    }

    read_impl!(u8, read_u8);
    read_impl!(u16, read_u16);
    read_impl!(u32, read_u32);
    read_impl!(u64, read_u64);
    read_impl!(u128, read_u128);
    read_impl!(usize, read_usize);

    read_impl!(i8, read_i8);
    read_impl!(i16, read_i16);
    read_impl!(i32, read_i32);
    read_impl!(i64, read_i64);
    read_impl!(i128, read_i128);
    read_impl!(isize, read_isize);
}

impl<R: Read + ?Sized> ReadVarintExt for R {}

impl From<Overflow> for Error {
    fn from(err: Overflow) -> Self {
        Error::other(err)
    }
}

struct Iter<R> {
    inner: Bytes<R>,
    err: Option<Error>,
}

impl<R> Iter<R> {
    const fn new(inner: Bytes<R>) -> Self {
        Self { inner, err: None }
    }
}

impl<R: Read> Iterator for Iter<R> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        match self.err {
            Some(_) => None,
            None => match self.inner.next()? {
                Ok(v) => Some(v),
                Err(err) => {
                    self.err = Some(err);
                    None
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TESTS: &[i128] = &[
        -1 << 127,
        (-1 << 127) + 1,
        -1 << 63,
        (-1 << 63) + 1,
        -1,
        0,
        1,
        2,
        10,
        20,
        63,
        64,
        65,
        127,
        128,
        129,
        255,
        256,
        257,
        (1 << 63) - 1,
        i128::MAX,
    ];

    macro_rules! test_impl {
        ($name:ident, $type:ty, $write:ident, $read:ident) => {
            #[test]
            fn $name() {
                fn test<F>(buf: &mut [u8], want: $type, name: &str, mut f: F)
                where
                    F: FnMut(&mut [u8], $type) -> Result<usize>,
                {
                    buf.fill(0xff);

                    let got = f(buf, want).unwrap_or_else(|_| {
                        panic!("`{name}({want}{})` should not fail", stringify!($type))
                    });
                    assert_eq!(
                        got,
                        want.encoded_len(),
                        "`{name}({want})` != encoded_len({want})"
                    );

                    let mut tmp = (&*buf);
                    let got = tmp
                        .$read()
                        .unwrap_or_else(|_| panic!("`{}` should not fail", stringify!($read)));
                    assert_eq!(got, want, "`{}`", stringify!($read));

                    let got = (&*buf).read_int::<$type>().unwrap_or_else(|_| {
                        panic!(
                            "`read_int::<{}>({want})` should not fail",
                            stringify!($type)
                        )
                    });
                    assert_eq!(got, want, "`read_int::<{}>`", stringify!($type));
                }

                let mut buf = vec![0x80u8; 100];
                for &x in TESTS {
                    let Ok(want) = x.try_into() else {
                        continue;
                    };
                    test(&mut buf, want, stringify!($write), |mut buf, want| {
                        buf.$write(want)
                    });
                    test(&mut buf, want, stringify!("write_int"), |mut buf, want| {
                        buf.write_int(want)
                    });
                }
            }
        };
    }
    test_impl!(test_io_u8, u8, write_u8, read_u8);
    test_impl!(test_io_u16, u16, write_u16, read_u16);
    test_impl!(test_io_u32, u32, write_u32, read_u32);
    test_impl!(test_io_u64, u64, write_u64, read_u64);
    test_impl!(test_io_u128, u128, write_u128, read_u128);
    test_impl!(test_io_usize, usize, write_usize, read_usize);

    test_impl!(test_io_i8, i8, write_i8, read_i8);
    test_impl!(test_io_i16, i16, write_i16, read_i16);
    test_impl!(test_io_i32, i32, write_i32, read_i32);
    test_impl!(test_io_i64, i64, write_i64, read_i64);
    test_impl!(test_io_i128, i128, write_i128, read_i128);
    test_impl!(test_io_isize, isize, write_isize, read_isize);
}
