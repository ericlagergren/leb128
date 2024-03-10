//! LEB128 (Little Endian Base 128) encoding.

mod io;
use core::{fmt, mem};

//#[cfg(feature = "std")]
pub use io::*;

/// Returns the number of bits needed to represent `x`.
macro_rules! bitlen {
    ($x:expr) => {{
        if $x == 0 {
            0
        } else {
            $x.ilog2() + 1
        }
    }};
}

/// Returns the number of bytes needed to encode `x`.
macro_rules! encoded_len {
    ($x:expr) => {{
        (1 + (bitlen!($x) - 1) / 7) as usize
    }};
}

/// Returns the maximum number of bytes needed to encode `T`.
const fn max_len<T>() -> usize {
    let bits = mem::size_of::<T>() * 8;
    (bits + 7 - 1) / 7
}

/// Returns the maximum last value in an encoded `T`.
const fn max_last_byte<T>() -> u8 {
    let bits = mem::size_of::<T>() * 8;
    (1 << (bits % 7)) - 1
}

mod private {
    use super::Overflow;

    pub trait Sealed: Sized {
        type Buf: Default + 'static;
        fn write(self, buf: &mut Self::Buf) -> &[u8];
        fn try_write(self, buf: &mut [u8]) -> Option<&[u8]>;
        fn read<I>(src: I) -> Result<(Self, usize), Overflow>
        where
            I: IntoIterator<Item = u8>;
    }

    pub trait Signed {
        type Unsigned;
        fn zigzag(self) -> Self::Unsigned;
    }

    pub trait Unsigned {
        type Signed;
        fn unzigzag(self) -> Self::Signed;
    }
}
pub(crate) use private::{Sealed, Signed, Unsigned};

/// An integer that can be LEB128-encoded.
pub trait Integer: Sealed {
    /// The maximum size in bytes of the LEB128-encoded integer.
    const MAX_LEN: usize;
}

/// Tries to encode `x` in LEB128 format.
///
/// It returns the portion of `buf` that was written to,
/// or `None` if `buf` is too small to fit `x`.
pub fn try_write<T: Integer>(buf: &mut [u8], x: T) -> Option<&[u8]> {
    x.try_write(buf)
}

/// Decodes a LEB128-encoded integer from `buf`.
///
/// It returns the decoded integer and the number of
/// bytes read.
pub fn read<T: Integer>(buf: &[u8]) -> Result<(T, usize), Overflow> {
    T::read(buf.iter().copied())
}

macro_rules! impl_integer {
    (
        $unsigned:ty,
        $uwrite:ident, $try_uwrite:ident, $uread:ident,
        $umax:ident,
        $signed:ty,
        $iwrite:ident, $try_iwrite:ident, $iread:ident,
        $imax:ident $(,)?
    ) => {
        impl Integer for $unsigned {
            const MAX_LEN: usize = max_len::<Self>();
        }

        impl Unsigned for $unsigned {
            type Signed = $signed;

            #[inline(always)]
            fn unzigzag(self) -> Self::Signed {
                ((self >> 1) as $signed)
                    ^ (self as $signed) << (Self::Signed::BITS - 1) >> (Self::Signed::BITS - 1)
            }
        }

        impl Sealed for $unsigned {
            type Buf = [u8; Self::MAX_LEN];

            fn write(mut self, buf: &mut Self::Buf) -> &[u8] {
                // The compiler can prove that all indexing is in
                // bounds.
                #![allow(clippy::indexing_slicing)]

                let mut i = 0;
                while self >= 0x80 {
                    buf[i] = (self as u8) | 0x80;
                    self >>= 7;
                    i += 1;
                }
                buf[i] = self as u8;
                &buf[..i + 1]
            }

            fn try_write(mut self, buf: &mut [u8]) -> Option<&[u8]> {
                let n = encoded_len!(self);
                let (last, rest) = buf.get_mut(..n)?.split_last_mut()?;
                for v in rest {
                    *v = (self as u8) | 0x80;
                    self >>= 7;
                }
                *last = self as u8;
                Some(buf)
            }

            fn read<I>(src: I) -> Result<(Self, usize), Overflow>
            where
                I: IntoIterator<Item = u8>,
            {
                let mut x = 0; // result
                let mut s = 0; // shift
                for (i, v) in src.into_iter().enumerate() {
                    if i == Self::MAX_LEN {
                        return Err(Overflow(i + 1));
                    }
                    if v < 0x80 {
                        if i == Self::MAX_LEN - 1 && v > max_last_byte::<Self>() {
                            return Err(Overflow(i + 1));
                        }
                        x |= (v as Self) << s;
                        return Ok((x, i + 1));
                    }
                    x |= ((v & 0x7f) as Self) << s;
                    s += 7;
                }
                Ok((0, 0))
            }
        }

        #[doc = "The maximum size in bytes of a LEB128-encoded `"]
        #[doc = stringify!($unsigned)]
        #[doc = "`."]
        pub const $umax: usize = <$unsigned>::MAX_LEN;

        /// Encodes `x` into `buf` in LEB128 format, returning
        /// the portion of `buf` that was written to.
        pub fn $uwrite(buf: &mut [u8; $umax], x: $unsigned) -> &[u8] {
            x.write(buf)
        }

        /// Tries to encode `x` in LEB128 format.
        ///
        /// It returns the portion of `buf` that was written to,
        /// or `None` if `buf` is too small to fit `x`.
        pub fn $try_uwrite(buf: &mut [u8], x: $unsigned) -> Option<&[u8]> {
            x.try_write(buf)
        }

        #[doc = "Decodes a LEB128-encoded `"]
        #[doc = stringify!($unsigned)]
        #[doc = "` from `buf`."]
        ///
        /// It returns the decoded integer and the number of
        /// bytes read.
        pub fn $uread(buf: &[u8]) -> Result<($unsigned, usize), Overflow> {
            <$unsigned>::read(buf.iter().copied())
        }

        impl Integer for $signed {
            const MAX_LEN: usize = max_len::<Self>();
        }

        impl Signed for $signed {
            type Unsigned = $unsigned;

            #[inline(always)]
            fn zigzag(self) -> Self::Unsigned {
                ((self << 1) ^ (self >> (Self::BITS - 1))) as Self::Unsigned
            }
        }

        impl Sealed for $signed {
            type Buf = [u8; Self::MAX_LEN];

            #[inline(always)]
            fn write(self, buf: &mut Self::Buf) -> &[u8] {
                self.zigzag().write(buf)
            }

            #[inline(always)]
            fn try_write(self, buf: &mut [u8]) -> Option<&[u8]> {
                self.zigzag().try_write(buf)
            }

            #[inline(always)]
            fn read<I>(src: I) -> Result<(Self, usize), Overflow>
            where
                I: IntoIterator<Item = u8>,
            {
                let (ux, n) = <$unsigned>::read(src)?;
                Ok((ux.unzigzag(), n))
            }
        }

        #[doc = "The maximum size in bytes of a LEB128-encoded `"]
        #[doc = stringify!($signed)]
        #[doc = "`."]
        pub const $imax: usize = <$signed>::MAX_LEN;

        /// Encodes `x` into `buf` in LEB128 format, returning
        /// the portion of `buf` that was written to.
        pub fn $iwrite(buf: &mut [u8; $imax], x: $signed) -> &[u8] {
            x.write(buf)
        }

        /// Tries to encode `x` in LEB128 format.
        ///
        /// It returns the portion of `buf` that was written to,
        /// or `None` if `buf` is too small to fit `x`.
        pub fn $try_iwrite(buf: &mut [u8], x: $signed) -> Option<&[u8]> {
            x.try_write(buf)
        }

        #[doc = "Decodes a LEB128-encoded `"]
        #[doc = stringify!($signed)]
        #[doc = "` from `buf`."]
        ///
        /// It returns the decoded integer and the number of
        /// bytes read.
        pub fn $iread(buf: &[u8]) -> Result<($signed, usize), Overflow> {
            <$signed>::read(buf.iter().copied())
        }
    };
}
impl_integer!(
    u8,
    write_u8,
    try_write_u8,
    read_u8,
    MAX_LEN_U8,
    i8,
    write_i8,
    try_write_i8,
    read_i8,
    MAX_LEN_I8
);
impl_integer!(
    u16,
    write_u16,
    try_write_u16,
    read_u16,
    MAX_LEN_U16,
    i16,
    write_i16,
    try_write_i16,
    read_i16,
    MAX_LEN_I16,
);
impl_integer!(
    u32,
    write_u32,
    try_write_u32,
    read_u32,
    MAX_LEN_U32,
    i32,
    write_i32,
    try_write_i32,
    read_i32,
    MAX_LEN_I32,
);
impl_integer!(
    u64,
    write_u64,
    try_write_u64,
    read_u64,
    MAX_LEN_U64,
    i64,
    write_i64,
    try_write_i64,
    read_i64,
    MAX_LEN_I64,
);
impl_integer!(
    u128,
    write_u128,
    try_write_u128,
    read_u128,
    MAX_LEN_U128,
    i128,
    write_i128,
    try_write_i128,
    read_i128,
    MAX_LEN_I128,
);
impl_integer!(
    usize,
    write_usize,
    try_write_usize,
    read_usize,
    MAX_LEN_USIZE,
    isize,
    write_isize,
    try_write_isize,
    read_isize,
    MAX_LEN_ISIZE,
);

/// The encoded integer overflows the type.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Overflow(
    /// The number of bytes read from the buffer.
    pub usize,
);

impl fmt::Display for Overflow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "integer overflow")
    }
}

// #[cfg(feature = "std")]
// #[cfg_attr(docs, doc(cfg(feature = "std")))]
impl std::error::Error for Overflow {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_byte() {
        for x in 0..=127u8 {
            let mut buf = [0u8; MAX_LEN_U8];
            let n = write_u8(&mut buf, x).len();
            assert_eq!(n, 1, "{x}");
            assert_eq!(buf, [x, 0], "{x}");
        }
    }

    macro_rules! test_max {
        ($name:ident, $write:ident, $read:ident, $type:ty) => {
            #[test]
            fn $name() {
                let mut buf = [0u8; <$type as Integer>::MAX_LEN];
                let nw = $write(&mut buf, <$type>::MAX).len();
                assert_eq!(nw, buf.len());
                let (got, nr) = $read(&buf).expect("should succeed");
                assert_eq!(nr, nw);
                assert_eq!(got, <$type>::MAX);
            }
        };
    }
    test_max!(test_max_u8, write_u8, read_u8, u8);
    test_max!(test_max_u16, write_u16, read_u16, u16);
    test_max!(test_max_u32, write_u32, read_u32, u32);
    test_max!(test_max_u64, write_u64, read_u64, u64);
    test_max!(test_max_u128, write_u128, read_u128, u128);
    test_max!(test_max_usize, write_usize, read_usize, usize);

    test_max!(test_max_i8, write_i8, read_i8, i8);
    test_max!(test_max_i16, write_i16, read_i16, i16);
    test_max!(test_max_i32, write_i32, read_i32, i32);
    test_max!(test_max_i64, write_i64, read_i64, i64);
    test_max!(test_max_i128, write_i128, read_i128, i128);
    test_max!(test_max_isize, write_isize, read_isize, isize);

    macro_rules! test_round_trip {
        ($name:ident, $write:ident, $read:ident, $type:ty) => {
            #[test]
            fn $name() {
                for x in 0..=<$type>::MAX {
                    let mut buf = [0u8; <$type as Integer>::MAX_LEN];
                    let nw = $write(&mut buf, x).len();
                    let (got, nr) = $read(&buf)
                        .unwrap_or_else(|err| panic!("#{x}: should succeed: {err:?} {buf:?}"));
                    assert_eq!(x, got, "#{x} {buf:?}");
                    assert_eq!(nr, nw, "#{x} {buf:?}");
                }
            }
        };
    }
    test_round_trip!(test_round_trip_u8, write_u8, read_u8, u8);
    test_round_trip!(test_round_trip_u16, write_u16, read_u16, u16);
    #[cfg(not(debug_assertions))]
    test_round_trip!(test_round_trip_u32, write_u32, read_u32, u32);

    test_round_trip!(test_round_trip_i8, write_i8, read_i8, i8);
    test_round_trip!(test_round_trip_i16, write_i16, read_i16, i16);
    #[cfg(not(debug_assertions))]
    test_round_trip!(test_round_trip_i32, write_i32, read_i32, i32);
}
