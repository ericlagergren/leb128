use core::{fmt, fmt::Debug, hash::Hash};

mod private {
    pub trait Sealed {}
}
pub(crate) use private::Sealed;

pub(crate) trait Util {
    type Unsigned;
    fn to_unsigned(self) -> Self::Unsigned;
}

/// An integer that can be LEB128-encoded.
pub trait Varint:
    Clone + Copy + Debug + Default + Eq + Hash + Ord + PartialEq + PartialOrd + Sized + Sealed
{
    /// The maximum size in bytes of the encoded integer.
    const MAX_LEN: usize;

    /// A fixed-size buffer.
    ///
    /// Is always `[u8; Self::MAX_LEN]`.
    type Buf: Default + 'static;

    /// Returns the number of bytes needed to encode the integer.
    fn encoded_len(self) -> usize;

    /// Decodes a LEB128-encoded integer from `buf`.
    ///
    /// It returns the decoded integer and the number of
    /// bytes read.
    fn read<I>(iter: I) -> Result<(Self, usize), Overflow>
    where
        I: IntoIterator<Item = u8>;

    /// Encodes `x` into `buf` in LEB128 format, returning
    /// the portion of `buf` that was written to.
    fn write(self, buf: &mut Self::Buf) -> &[u8];

    /// Tries to encode `x` in LEB128 format.
    ///
    /// It returns the portion of `buf` that was written to,
    /// or `None` if `buf` is too small to fit `x`.
    ///
    /// In order to succeed, `buf` should be at least
    /// [`encoded_len`][Self::encoded_len] bytes.
    fn try_write(self, buf: &mut [u8]) -> Option<&[u8]>;
}

macro_rules! zigzag {
    ($unsigned:ty : $x:ident) => {{
        (($x << 1) ^ ($x >> (<$unsigned>::BITS - 1))) as $unsigned
    }};
}

macro_rules! unzigzag {
    ($signed:ty : $x:ident) => {{
        (($x >> 1) as $signed) ^ ($x as $signed) << (<$signed>::BITS - 1) >> (<$signed>::BITS - 1)
    }};
}

macro_rules! encoded_len {
    (u8: $x:expr) => {{
        if $x > 0x7f {
            2
        } else {
            1
        }
    }};
    ($ty:ty : $x:expr) => {{
        match $x {
            v => {
                let _: $ty = v;
                if cfg!(target_arch = "x86_64") {
                    // OR in 1 to avoid branching.
                    let nlz = (1 | $x).leading_zeros();
                    let bits = (<$ty>::BITS - 1) - nlz;
                    ((bits * 9 + (64 + 9)) / 64) as usize
                } else {
                    let nlz = $x.leading_zeros();
                    (((<$ty>::BITS * 9 + 64) - (nlz * 9)) / 64) as usize
                }
            }
        }
    }};
}

macro_rules! read_uvarint {
    ($ty:ty : $src:expr) => {{
        /// The maximum last byte in an encoded integer.
        const MAX_LAST_BYTE: u8 = (1 << (<$ty>::BITS % 7)) - 1;

        let mut x: $ty = 0; // result
        let mut s = 0; // shift
        for (i, v) in $src.into_iter().enumerate() {
            if i == <$ty as Varint>::MAX_LEN {
                return Err(Overflow(i + 1));
            }
            if v < 0x80 {
                if i == <$ty as Varint>::MAX_LEN - 1 && v > MAX_LAST_BYTE {
                    return Err(Overflow(i + 1));
                }
                x |= (v as $ty) << s;
                return Ok((x, i + 1));
            }
            x |= ((v & 0x7f) as $ty) << s;
            s += 7;
        }
        Ok((0, 0))
    }};
}

macro_rules! write_uvarint {
    ($ty:ty : $x:expr, $buf:expr) => {{
        // The compiler can prove that all indexing is in
        // bounds.
        #![allow(clippy::indexing_slicing)]

        match ($x, $buf) {
            (mut x, buf) => {
                let _: &[u8; <$ty as Varint>::MAX_LEN] = &buf;

                let mut i = 0;
                while x >= 0x80 {
                    buf[i] = (x as u8) | 0x80;
                    x >>= 7;
                    i += 1;
                }
                buf[i] = x as u8;
                &buf[..i + 1]
            }
        }
    }};
}

macro_rules! try_write_uvarint {
    ($ty:ty : $x:expr, $buf:expr) => {{
        match ($x, $buf) {
            (mut x, buf) => {
                let _: $ty = x;
                let _: &mut [u8] = buf;

                let n = x.encoded_len();
                let (last, rest) = buf.get_mut(..n)?.split_last_mut()?;
                for v in rest {
                    *v = (x as u8) | 0x80;
                    x >>= 7;
                }
                *last = x as u8;
                Some(buf)
            }
        }
    }};
}

macro_rules! impl_varint {
    ($unsigned:ty => $signed:ty) => {
        impl Sealed for $unsigned {}
        impl Varint for $unsigned {
            const MAX_LEN: usize = ((<$unsigned>::BITS + 6) / 7) as usize;
            type Buf = [u8; Self::MAX_LEN];
            fn encoded_len(self) -> usize {
                encoded_len!($unsigned: self)
            }
            fn read<I>(iter: I) -> Result<(Self, usize), Overflow>
            where
                I: IntoIterator<Item=u8>,
            {
                read_uvarint!($unsigned: iter)
            }
            fn write(self, buf: &mut Self::Buf) -> &[u8] {
                write_uvarint!($unsigned: self, buf)
            }
            fn try_write(self, buf: &mut [u8]) -> Option<&[u8]> {
                try_write_uvarint!($unsigned: self, buf)
            }
        }
        impl Util for $unsigned {
            type Unsigned = $unsigned;
            fn to_unsigned(self) -> Self::Unsigned {
                self
            }
        }

        impl Sealed for $signed {}
        impl Varint for $signed {
            const MAX_LEN: usize = ((<$signed>::BITS + 6) / 7) as usize;
            type Buf = [u8; Self::MAX_LEN];
            fn encoded_len(self) -> usize {
                zigzag!($unsigned: self).encoded_len()
            }
            fn read<I>(iter: I) -> Result<(Self, usize), Overflow>
            where
                I: IntoIterator<Item=u8>,
            {
                let (ux, n) = read_uvarint!($signed: iter)?;
                Ok((unzigzag!($signed: ux), n))
            }
            fn write(self, buf: &mut Self::Buf) -> &[u8] {
                zigzag!($unsigned: self).write(buf)
            }
            fn try_write(self, buf: &mut [u8]) -> Option<&[u8]> {
                zigzag!($unsigned: self).try_write(buf)
            }
        }
        impl Util for $signed {
            type Unsigned = $unsigned;
            fn to_unsigned(self) -> Self::Unsigned {
                zigzag!($unsigned: self)
            }
        }
    }
}
impl_varint!(u8 => i8);
impl_varint!(u16 => i16);
impl_varint!(u32 => i32);
impl_varint!(u64 => i64);
impl_varint!(u128 => i128);
impl_varint!(usize => isize);

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
