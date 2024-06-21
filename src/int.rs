use core::{fmt, fmt::Debug, hash::Hash};

mod private {
    use super::Overflow;

    pub trait Sealed: Copy + Sized {
        /// The size of the integer in bits.
        const BITS: u32;

        /// The maximum size in bytes of the encoded integer.
        const MAX_LEN: usize = ((Self::BITS + 6) / 7) as usize;

        /// The maximum last byte in an encoded integer.
        const MAX_LAST_BYTE: u8 = (1 << (Self::BITS % 7)) - 1;

        /// A fixed-size buffer.
        ///
        /// Is always `[u8; Self::MAX_LEN]`.
        type Buf: Default + 'static;

        /// Returns the number of bytes needed to encode the
        /// number.
        fn encoded_len(&self) -> usize;

        /// Writes itself to `buf` and returns the slice of `buf`
        /// that was written to.
        fn write(self, buf: &mut Self::Buf) -> &[u8];

        /// Like [`write`][Self::write], but returns `None` if
        /// `buf` is too small.
        fn try_write(self, buf: &mut [u8]) -> Option<&[u8]>;

        /// Reads itself from `src`.
        fn read<I>(src: I) -> Result<(Self, usize), Overflow>
        where
            I: IntoIterator<Item = u8>;
    }

    /// A signed integer.
    pub trait Signed: Sealed {
        /// The corresponding unsigned type.
        type Unsigned;

        fn zigzag(self) -> Self::Unsigned;
    }

    /// An unsigned integer.
    pub trait Unsigned: Sealed {
        /// The corresponding signed type.
        type Signed;

        fn unzigzag(self) -> Self::Signed;
    }
}
pub(crate) use private::{Sealed, Signed, Unsigned};

/// An integer that can be LEB128-encoded.
pub trait Integer:
    Clone + Copy + Debug + Default + Eq + Hash + Ord + PartialEq + PartialOrd + Sealed
{
}

/// Returns the number of bytes needed to encode this
/// [`Integer`].
pub const fn max_len<T: Integer>() -> usize {
    T::MAX_LEN
}

/// Returns the number of bytes needed to encode the number.
pub fn encoded_len<T: Integer>(x: T) -> usize {
    x.encoded_len()
}

/// Tries to encode `x` in LEB128 format.
///
/// It returns the portion of `buf` that was written to,
/// or `None` if `buf` is too small to fit `x`.
///
/// In order to succeed, `buf` should be at least [`encoded_len`]
/// bytes.
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
        impl Integer for $unsigned {}

        impl Unsigned for $unsigned {
            type Signed = $signed;

            #[inline(always)]
            fn unzigzag(self) -> Self::Signed {
                ((self >> 1) as $signed)
                    ^ (self as $signed) << (Self::Signed::BITS - 1) >> (Self::Signed::BITS - 1)
            }
        }

        impl Sealed for $unsigned {
            const BITS: u32 = <$unsigned>::BITS;

            type Buf = [u8; Self::MAX_LEN];

            fn encoded_len(&self) -> usize {
                if cfg!(target_arch = "x86_64") {
                    // OR in 1 to avoid branching.
                    let nlz = (1 | self).leading_zeros();
                    let bits = (Self::BITS - 1) - nlz;
                    ((bits * 9 + (64 + 9)) / 64) as usize
                } else {
                    let nlz = self.leading_zeros();
                    (((Self::BITS * 9 + 64) - (nlz * 9)) / 64) as usize
                }
            }

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
                let n = self.encoded_len();
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
                        if i == Self::MAX_LEN - 1 && v > Self::MAX_LAST_BYTE {
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
        ///
        /// In order to succeed, `buf` should be at least
        /// [`encoded_len`] bytes.
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

        impl Integer for $signed {}

        impl Signed for $signed {
            type Unsigned = $unsigned;

            #[inline(always)]
            fn zigzag(self) -> Self::Unsigned {
                ((self << 1) ^ (self >> (Self::BITS - 1))) as Self::Unsigned
            }
        }

        impl Sealed for $signed {
            const BITS: u32 = <$signed>::BITS;

            type Buf = [u8; Self::MAX_LEN];

            #[inline(always)]
            fn encoded_len(&self) -> usize {
                self.zigzag().encoded_len()
            }

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
        f.write_str("integer overflow")
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docs, doc(cfg(feature = "std")))]
impl std::error::Error for Overflow {}
