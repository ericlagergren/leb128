// #![cfg(feature = "std")]
// #![cfg_attr(docs, doc(cfg(feature = "std")))]

use std::io::{Bytes, Error, Read, Result, Write};

use super::{Integer, Overflow};

macro_rules! write_impl {
    ($type:ty, $name:ident) => {
        #[doc = "Writes a LEB128-encoded `"]
        #[doc = stringify!($type)]
        #[doc = "`."]
        fn $name(&mut self, x: $type) -> Result<()> {
            self.write_int(x)
        }
    };
}

/// Extends [`Write`] with methods for reading LEB128-encoded
/// integers.
pub trait WriteExt: Write {
    /// Writes a LEB128-encoded integer.
    fn write_int<T: Integer>(&mut self, x: T) -> Result<()> {
        let mut buf = T::Buf::default();
        self.write_all(x.write(&mut buf))
    }

    write_impl!(u8, write_u8);
    write_impl!(u16, write_u16);
    write_impl!(u32, write_u32);
    write_impl!(u64, write_u64);
    write_impl!(u128, write_u128);

    write_impl!(i8, write_i8);
    write_impl!(i16, write_i16);
    write_impl!(i32, write_i32);
    write_impl!(i64, write_i64);
    write_impl!(i128, write_i128);
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

impl<W: Write + ?Sized> WriteExt for W {}

/// Extends [`Read`] with methods for reading LEB128-encoded
/// integers.
pub trait ReadExt: Read {
    /// Reads a LEB128-encoded integer.
    fn read_int<T: Integer>(&mut self) -> Result<T> {
        let mut iter = Iter {
            inner: self.bytes(),
            err: None,
        };
        let (v, _) = T::read(&mut iter).map_err(Error::other)?;
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

    read_impl!(i8, read_i8);
    read_impl!(i16, read_i16);
    read_impl!(i32, read_i32);
    read_impl!(i64, read_i64);
    read_impl!(i128, read_i128);
}

impl<R: Read + ?Sized> ReadExt for R {}

impl From<Overflow> for Error {
    fn from(err: Overflow) -> Self {
        Error::other(err)
    }
}

struct Iter<R> {
    inner: Bytes<R>,
    err: Option<Error>,
}

impl<R: Read> Iterator for Iter<R> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok(v) => Some(v),
            Err(err) => {
                self.err = Some(err);
                None
            }
        }
    }
}
