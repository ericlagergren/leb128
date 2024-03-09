// #![cfg(feature = "std")]
// #![cfg_attr(docs, doc(cfg(feature = "std")))]

use std::io::{Error, Read, Result, Write};

use crate::{Integer, Overflow};

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
pub trait WriteLeb128Ext: Write {
    /// Writes a LEB128-encoded integer.
    fn write_int<T: Integer>(&mut self, x: T) -> Result<()> {
        let mut buf = T::Buf::default();
        let n = x.write(&mut buf);
        self.write_all(&buf.as_ref()[..n])
    }

    write_impl!(u8, read_u8);
    write_impl!(u16, read_u16);
    write_impl!(u32, read_u32);
    write_impl!(u64, read_u64);
    write_impl!(u128, read_u128);

    write_impl!(i8, read_i8);
    write_impl!(i16, read_i16);
    write_impl!(i32, read_i32);
    write_impl!(i64, read_i64);
    write_impl!(i128, read_i128);
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

/// Extends [`Read`] with methods for reading LEB128-encoded
/// integers.
pub trait ReadLeb128Ext: Read {
    /// Reads a LEB128-encoded integer.
    fn read_int<T: Integer>(&mut self) -> Result<T> {
        T::read(self.bytes())
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

impl From<Overflow> for Error {
    fn from(err: Overflow) -> Self {
        Error::other(err)
    }
}
