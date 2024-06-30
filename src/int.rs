use core::{
    fmt::{self, Debug},
    hash::Hash,
    iter::{ExactSizeIterator, FusedIterator},
};

mod private {
    use core::{fmt::Debug, hash::Hash};

    pub trait Sealed {}
    pub trait Integer: Sealed {
        type Unsigned: Clone
            + Copy
            + Debug
            + Default
            + Eq
            + Hash
            + Ord
            + PartialEq
            + PartialOrd
            + Sized;
        fn to_unsigned(self) -> Self::Unsigned;
    }
}
pub(crate) use private::{Integer, Sealed};

/// An integer that can be LEB128-encoded.
///
/// It is implemented by all [integer types], including `usize`
/// and `isize`.
///
/// # Example
///
/// ```rust
/// use rust_leb128::Varint;
///
/// let x: u64 = 12009733384289536743;
/// let mut buf = [0u8; u64::MAX_LEN];
/// let got = x.write(&mut buf);
/// let want = [
///     0xe7, 0x95, 0xe9, 0xcd,
///     0x9f, 0x9c, 0xc9, 0xd5,
///     0xa6, 0x1,
/// ];
/// assert_eq!(got, want);
/// ```
///
/// [integer types]: https://doc.rust-lang.org/reference/types/numeric.html#integer-types
pub trait Varint:
    Clone + Copy + Debug + Default + Eq + Hash + Ord + PartialEq + PartialOrd + Sized + Integer
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
    fn read(buf: &[u8]) -> Result<(Self, usize), Overflow>;

    /// Decodes a LEB128-encoded integer from `iter`.
    ///
    /// It returns the decoded integer and the number of
    /// bytes read.
    fn read_iter<I>(iter: I) -> Result<(Self, usize), Overflow>
    where
        I: IntoIterator<Item = u8>;

    /// Encodes itself into `buf` in LEB128 format, returning
    /// the portion of `buf` that was written to.
    fn write(self, buf: &mut Self::Buf) -> &[u8];

    /// Tries to encode itself in LEB128 format.
    ///
    /// It returns the portion of `buf` that was written to,
    /// or `None` if `buf` is too small to fit `x`.
    ///
    /// In order to succeed, `buf` should be at least
    /// [`encoded_len`][Self::encoded_len] bytes.
    fn try_write(self, buf: &mut [u8]) -> Option<&[u8]>;

    /// Returns an interator over the bytes of the LEB128 encoded
    /// integer.
    fn into_iter(self) -> Iter<Self>;
}

macro_rules! zigzag {
    ($unsigned:ty : $x:expr) => {{
        match $x {
            // Zigzag encoding handles sign loss.
            #[allow(clippy::cast_sign_loss)]
            v => ((v << 1) ^ (v >> (<$unsigned>::BITS - 1))) as $unsigned,
        }
    }};
}

macro_rules! unzigzag {
    ($signed:ty : $x:expr) => {{
        match $x {
            // `(v>>1) as $signed` cannot wrap since we're
            // shifting off one bit.
            //
            // `v as $signed` might wrap but it's okay.
            #[allow(clippy::cast_possible_wrap)]
            v => {
                ((v >> 1) as $signed)
                    ^ (v as $signed) << (<$signed>::BITS - 1) >> (<$signed>::BITS - 1)
            }
        }
    }};
}

macro_rules! encoded_len {
    // For everything except `u8` and `u128`.
    (@def $ty:ty: $x:expr) => {{
        match $x {
            v => {
                // 73/512 approximates 1/7. Other implementations
                // use 9/64, but it's too inaccurate for `u128`.
                const N: u32 = 73;
                const D: u32 = 512;

                let _: $ty = v;
                if cfg!(target_arch = "x86_64") {
                    // OR in 1 to avoid branching.
                    let nlz = (1 | $x).leading_zeros();
                    let bits = (<$ty>::BITS - 1) - nlz;
                    ((bits * N + (D + N)) / D) as usize
                } else {
                    let nlz = $x.leading_zeros();
                    (((<$ty>::BITS * N + D) - (nlz * N)) / D) as usize
                }
            }
        }
    }};
    (@u8: $x:expr) => {{
        match $x {
            // Same as `if v > 0x7f { 2 } else { 1 }`, but the
            // compiler generates better code.
            v => usize::from(v > 0x7f) + 1
        }
    }};
    (@u16: $x:expr) => { encoded_len!(@def u16: $x) };
    (@u32: $x:expr) => { encoded_len!(@def u32: $x) };
    (@u64: $x:expr) => { encoded_len!(@def u64: $x) };
    (@u128: $x:expr) => { encoded_len!(@def u128: $x) };
    (@usize: $x:expr) => { encoded_len!(@def usize: $x) };
    ($ty:tt: $x:expr) => { encoded_len!(@ $ty: $x) };
}

macro_rules! read_uvarint {
    (@imp $ty:ty : $src:expr) => {{
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
                x |= <$ty>::from(v) << s;
                return Ok((x, i + 1));
            }
            x |= <$ty>::from(v & 0x7f) << s;
            s += 7;
        }
        Ok((0, 0))
    }};
    (@u8: $src:expr) => { read_uvarint!(@imp u8: $src) };
    (@u16: $src:expr) => { read_uvarint!(@imp u16: $src) };
    (@u32: $src:expr) => { read_uvarint!(@imp u32: $src) };
    (@u64: $src:expr) => { read_uvarint!(@imp u64: $src) };
    (@u128: $src:expr) => { read_uvarint!(@imp u128: $src) };
    (@usize: $src:expr) => { read_uvarint!(@imp usize: $src) };
    ($ty:tt: $src:expr) => { read_uvarint!(@ $ty: $src) };
}

macro_rules! write_uvarint {
    (@imp $ty:ty : $x:expr, $buf:expr) => {{
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
    (@u8: $x:expr, $buf:expr) => { write_uvarint!(@imp u8: $x, $buf) };
    (@u16: $x:expr, $buf:expr) => { write_uvarint!(@imp u16: $x, $buf) };
    (@u32: $x:expr, $buf:expr) => { write_uvarint!(@imp u32: $x, $buf) };
    (@u64: $x:expr, $buf:expr) => { write_uvarint!(@imp u64: $x, $buf) };
    (@u128: $x:expr, $buf:expr) => { write_uvarint!(@imp u128: $x, $buf) };
    (@usize: $x:expr, $buf:expr) => { write_uvarint!(@imp usize: $x, $buf) };
    ($ty:tt: $x:expr, $buf:expr) => { write_uvarint!(@ $ty: $x, $buf) };
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

macro_rules! impl_iter {
    ($ty:ty) => {
        impl Iterator for Iter<$ty> {
            type Item = u8;

            fn next(&mut self) -> Option<Self::Item> {
                let x = self.v?;
                let mut b = (x as u8);
                if x >= 0x80 {
                    b |= 0x80;
                    self.v = Some(x >> 7);
                } else {
                    self.v = None;
                }
                Some(b)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                match self.v {
                    Some(v) => {
                        let n = v.encoded_len();
                        (n, Some(n))
                    }
                    None => (0, None),
                }
            }
        }

        impl FusedIterator for Iter<$ty> {}

        impl ExactSizeIterator for Iter<$ty> {
            fn len(&self) -> usize {
                match self.v {
                    Some(v) => v.encoded_len(),
                    None => 0,
                }
            }
        }
    };
}

macro_rules! impl_varint {
    ($unsigned:tt, $signed:tt) => {
        impl Sealed for $unsigned {}
        impl Integer for $unsigned {
            type Unsigned = $unsigned;
            fn to_unsigned(self) -> Self::Unsigned {
                self
            }
        }
        impl Varint for $unsigned {
            const MAX_LEN: usize = ((<$unsigned>::BITS + 6) / 7) as usize;
            type Buf = [u8; Self::MAX_LEN];
            fn encoded_len(self) -> usize {
                encoded_len!($unsigned: self)
            }
            fn read(buf: &[u8]) -> Result<(Self, usize), Overflow> {
                read_uvarint!($unsigned: buf.iter().copied())
            }
            fn read_iter<I>(iter: I) -> Result<(Self, usize), Overflow>
            where
                I: IntoIterator<Item = u8>,
            {
                read_uvarint!($unsigned: iter)
            }
            fn write(self, buf: &mut Self::Buf) -> &[u8] {
                write_uvarint!($unsigned: self, buf)
            }
            fn try_write(self, buf: &mut [u8]) -> Option<&[u8]> {
                try_write_uvarint!($unsigned: self, buf)
            }
            fn into_iter(self) -> Iter<Self> {
                Iter { v: Some(self) }
            }
        }
        impl_iter!($unsigned);

        impl Sealed for $signed {}
        impl Integer for $signed {
            type Unsigned = $unsigned;
            fn to_unsigned(self) -> Self::Unsigned {
                zigzag!($unsigned: self)
            }
        }
        impl Varint for $signed {
            const MAX_LEN: usize = ((<$signed>::BITS + 6) / 7) as usize;
            type Buf = [u8; Self::MAX_LEN];
            fn encoded_len(self) -> usize {
                zigzag!($unsigned: self).encoded_len()
            }
            fn read(buf: &[u8]) -> Result<(Self, usize), Overflow> {
                let (ux, n) = <$unsigned>::read(buf)?;
                Ok((unzigzag!($signed: ux), n))
            }
            fn read_iter<I>(iter: I) -> Result<(Self, usize), Overflow>
            where
                I: IntoIterator<Item = u8>,
            {
                let (ux, n) = <$unsigned>::read_iter(iter)?;
                Ok((unzigzag!($signed: ux), n))
            }
            fn write(self, buf: &mut Self::Buf) -> &[u8] {
                zigzag!($unsigned: self).write(buf)
            }
            fn try_write(self, buf: &mut [u8]) -> Option<&[u8]> {
                zigzag!($unsigned: self).try_write(buf)
            }
            fn into_iter(self) -> Iter<Self> {
                Iter { v: Some(self.to_unsigned()) }
            }
        }
        impl_iter!($signed);
    }
}
impl_varint!(u8, i8);
impl_varint!(u16, i16);
impl_varint!(u32, i32);
impl_varint!(u64, i64);
impl_varint!(u128, i128);
impl_varint!(usize, isize);

/// An iterator over the bytes in a LEB128 encoded [`Varint`].
#[derive(Clone, Debug)]
#[must_use]
pub struct Iter<T: Varint> {
    v: Option<T::Unsigned>,
}

/// The encoded integer overflows the type.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Overflow(
    /// The number of bytes read from the buffer.
    pub usize,
);

impl fmt::Display for Overflow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("varint overflow")
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for Overflow {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test encoding a single byte < 128, which should encode
    /// as is.
    #[test]
    fn test_single_byte() {
        for x in 0..=127u8 {
            let mut buf = [0u8; u8::MAX_LEN];
            let n = x.write(&mut buf).len();
            assert_eq!(n, 1, "{x}");
            assert_eq!(buf, [x, 0], "{x}");
        }
    }

    /// Tests that we approximate 1/7 well enough for `u128`.
    #[test]
    fn test_encoded_len_u128() {
        let mut buf = [0u8; u128::MAX_LEN];
        let got = (u128::MAX / 2).write(&mut buf).len();
        let want = (u128::MAX / 2).encoded_len();
        assert_eq!(got, want);
    }

    macro_rules! test_encoded_len_exhaustive {
        (
            $(#[$meta:meta])*
            $name:ident, $ty:ty
        ) => {
            /// Exhaustive test for a `encoded_len!`.
            #[test]
            $(#[$meta])*
            fn $name() {
                const fn size_varint(mut x: $ty) -> usize {
                    let mut s = 1;
                    while x >= 128 {
                        s += 1;
                        x >>= 7;
                    }
                    s
                }
                for i in 0..<$ty>::MAX {
                    let got = i.encoded_len();
                    assert_eq!(got, size_varint(i), "#{i}");
                }
            }
        };
    }
    test_encoded_len_exhaustive!(test_encoded_len_u8_exhaustive, u8);
    test_encoded_len_exhaustive!(test_encoded_len_u16_exhaustive, u16);
    test_encoded_len_exhaustive!(
        #[cfg(not(any(miri, debug_assertions)))]
        test_encoded_len_u32_exhaustive,
        u32
    );

    macro_rules! test_max {
        ($name:ident, $ty:ty) => {
            #[test]
            fn $name() {
                let mut buf = [0u8; <$ty as Varint>::MAX_LEN];
                let nw = <$ty>::MAX.write(&mut buf).len();
                assert_eq!(nw, buf.len());
                let got = <$ty>::read(&buf);
                assert_eq!(got, Ok((<$ty>::MAX, nw)));
            }
        };
    }
    test_max!(test_max_u8, u8);
    test_max!(test_max_u16, u16);
    test_max!(test_max_u32, u32);
    test_max!(test_max_u64, u64);
    test_max!(test_max_u128, u128);
    test_max!(test_max_usize, usize);

    test_max!(test_max_i8, i8);
    test_max!(test_max_i16, i16);
    test_max!(test_max_i32, i32);
    test_max!(test_max_i64, i64);
    test_max!(test_max_i128, i128);
    test_max!(test_max_isize, isize);

    macro_rules! test_round_trip {
        ($name:ident, $ty:ty) => {
            #[test]
            fn $name() {
                for x in 0..=<$ty>::MAX {
                    let mut buf = [0u8; <$ty as Varint>::MAX_LEN];
                    let nw = x.write(&mut buf).len();
                    let got = <$ty>::read(&buf);
                    let want = Ok((x, nw));
                    assert_eq!(got, want, "#{x}");

                    let got = <$ty>::read_iter(x.into_iter());
                    assert_eq!(got, want);
                }
            }
        };
    }
    test_round_trip!(test_round_trip_u8, u8);
    test_round_trip!(test_round_trip_u16, u16);
    #[cfg(not(debug_assertions))]
    test_round_trip!(test_round_trip_u32, u32);

    test_round_trip!(test_round_trip_i8, i8);
    test_round_trip!(test_round_trip_i16, i16);
    #[cfg(not(debug_assertions))]
    test_round_trip!(test_round_trip_i32, i32);

    macro_rules! test_overflow {
        ($name:ident, $ty:ty) => {
            #[test]
            fn $name() {
                const MAX_LAST_BYTE: u8 = (1 << (<$ty>::BITS % 7)) - 1;
                let tests: [(Vec<u8>, &[u8], usize); 4] = [
                    // Last byte is too large.
                    (
                        vec![0x80; <$ty>::MAX_LEN - 1],
                        &[MAX_LAST_BYTE + 1],
                        <$ty>::MAX_LEN,
                    ),
                    // Encoded varint is too large.
                    (vec![0x80; <$ty>::MAX_LEN + 1], &[], <$ty>::MAX_LEN + 1),
                    // Last byte is too large.
                    (
                        vec![0xff; <$ty>::MAX_LEN - 1],
                        &[MAX_LAST_BYTE + 1],
                        <$ty>::MAX_LEN,
                    ),
                    // Encoded varint is too large.
                    (vec![0xff; <$ty>::MAX_LEN + 1], &[], <$ty>::MAX_LEN + 1),
                ];
                for (i, (mut input, extra, nr)) in tests.into_iter().enumerate() {
                    input.extend_from_slice(extra);
                    let got = <$ty>::read(&input);
                    let want = Err(Overflow(nr));
                    assert_eq!(got, want, "#{i}");
                }
            }
        };
    }
    test_overflow!(test_overflow_u8, u8);
    test_overflow!(test_overflow_u16, u16);
    test_overflow!(test_overflow_u32, u32);
    test_overflow!(test_overflow_u64, u64);
    test_overflow!(test_overflow_u128, u128);
    test_overflow!(test_overflow_usize, usize);

    test_overflow!(test_overflow_i8, i8);
    test_overflow!(test_overflow_i16, i16);
    test_overflow!(test_overflow_i32, i32);
    test_overflow!(test_overflow_i64, i64);
    test_overflow!(test_overflow_i128, i128);
    test_overflow!(test_overflow_isize, isize);
}
