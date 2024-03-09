use core::{fmt, mem};

mod private {
    use super::Overflow;

    pub trait Sealed: Sized {
        type Buf: AsRef<[u8]> + Default + 'static;
        fn write(self, buf: &mut Self::Buf) -> usize;
        fn try_write(self, buf: &mut [u8]) -> Option<usize>;
        fn read<I, E>(src: I) -> Result<Self, E>
        where
            I: IntoIterator<Item = Result<u8, E>>,
            E: From<Overflow>;
    }
}
pub(crate) use private::Sealed;

/// An integer that can be LEB128-encoded.
pub trait Integer: Sealed {
    /// The maximum size in bytes of the LEB128-encoded integer.
    const MAX_LEN: usize;
}

trait ByteRead {
    type Error: From<Overflow>;
    fn read_byte(&mut self) -> Result<Option<u8>, Self::Error>;
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
            const MAX_LEN: usize = $umax;
        }
        impl Sealed for $unsigned {
            type Buf = [u8; $umax];

            fn write(self, buf: &mut Self::Buf) -> usize {
                $uwrite(buf, self)
            }

            fn try_write(self, buf: &mut [u8]) -> Option<usize> {
                $try_uwrite(buf, self)
            }

            fn read<I, E>(src: I) -> Result<Self, E>
            where
                I: IntoIterator<Item = Result<u8, E>>,
                E: From<Overflow>,
            {
                let mut x = 0; // result
                let mut s = 0; // shift
                for (i, v) in src.into_iter().enumerate() {
                    let v = v?;
                    if i == $umax {
                        return Err(Overflow(i + 1).into());
                    }
                    if v < 0x80 {
                        if i == $umax - 1 && v > max_last_byte::<$unsigned>() {
                            return Err(Overflow(i + 1).into());
                        }
                        x |= (v as $unsigned) << s;
                        return Ok(x);
                    }
                    x |= ((v & 0x7f) as $unsigned) << s;
                    s += 7;
                }
                Ok(0)
            }
        }

        #[doc = "The maximum size in bytes of a LEB128-encoded `"]
        #[doc = stringify!($unsigned)]
        #[doc = "`."]
        pub const $umax: usize = max_len::<$unsigned>();

        /// Encodes `x` in LEB128 format, returning the number
        /// of bytes written to `buf`.
        pub fn $uwrite(buf: &mut [u8; $umax], mut x: $unsigned) -> usize {
            let mut i = 0;
            while x >= 0x80 {
                buf[i] = (x as u8) | 0x80;
                x >>= 7;
                i += 1;
            }
            buf[i] = x as u8;
            i + 1
        }

        /// Tries to encode `x` in LEB128 format.
        ///
        /// It returns the number of bytes written to `buf`, or
        /// `None` if `buf` is too small to fit `x`.
        pub fn $try_uwrite(buf: &mut [u8], x: $unsigned) -> Option<usize> {
            let mut tmp = [0u8; $umax];
            let n = $uwrite(&mut tmp, x);
            buf.get_mut(..n)?.copy_from_slice(&tmp[..n]);
            Some(n)
        }

        #[doc = "Decodes a LEB128-encoded `"]
        #[doc = stringify!($unsigned)]
        #[doc = "` from `buf`."]
        ///
        /// It returns the decoded integer and the number of
        /// bytes read.
        pub const fn $uread(buf: &[u8]) -> Result<($unsigned, usize), Overflow> {
            let mut x = 0; // result
            let mut s = 0; // shift
            let mut i = 0;
            while i < buf.len() {
                // The compiler can prove that this does not
                // panic since we checked `i < buf.len()`.
                #[allow(clippy::indexing_slicing)]
                let v = buf[i];
                if i == $umax {
                    return Err(Overflow(i + 1));
                }
                if v < 0x80 {
                    if i == $umax - 1 && v > max_last_byte::<$unsigned>() {
                        return Err(Overflow(i + 1));
                    }
                    x |= (v as $unsigned) << s;
                    return Ok((x, i + 1));
                }
                x |= ((v & 0x7f) as $unsigned) << s;
                s += 7;
                i += 1;
            }
            Ok((0, 0))
        }

        impl Integer for $signed {
            const MAX_LEN: usize = $imax;
        }
        impl Sealed for $signed {
            type Buf = [u8; $imax];

            fn write(self, buf: &mut Self::Buf) -> usize {
                $iwrite(buf, self)
            }

            fn try_write(self, buf: &mut [u8]) -> Option<usize> {
                $try_iwrite(buf, self)
            }

            fn read<I, E>(src: I) -> Result<Self, E>
            where
                I: IntoIterator<Item = Result<u8, E>>,
                E: From<Overflow>,
            {
                let ux = <$unsigned as Sealed>::read(src)?;
                let mut x = (ux >> 1) as $signed;
                if ux & 1 != 0 {
                    x = !x;
                }
                Ok(x)
            }
        }

        #[doc = "The maximum size in bytes of a LEB128-encoded `"]
        #[doc = stringify!($signed)]
        #[doc = "`."]
        pub const $imax: usize = max_len::<$signed>();

        /// Encodes `x` in LEB128 format and returns the number
        /// of bytes written to `buf`.
        pub fn $iwrite(buf: &mut [u8; $imax], x: $signed) -> usize {
            let mut ux = (x as $unsigned) << 1;
            if x < 0 {
                ux ^= ux;
            }
            $uwrite(buf, ux)
        }

        /// Tries to encode `x` in LEB128 format.
        ///
        /// It returns the number of bytes written to `buf`, or
        /// `None` if `buf` is too small to fit `x`.
        pub fn $try_iwrite(buf: &mut [u8], x: $signed) -> Option<usize> {
            let mut tmp = [0u8; $imax];
            let n = $iwrite(&mut tmp, x);
            buf.get_mut(..n)?.copy_from_slice(&tmp[..n]);
            Some(n)
        }

        #[doc = "Decodes a LEB128-encoded `"]
        #[doc = stringify!($signed)]
        #[doc = "` from `buf`."]
        ///
        /// It returns the decoded integer and the number of
        /// bytes read.
        pub const fn $iread(buf: &[u8]) -> Result<($signed, usize), Overflow> {
            let (ux, n) = match $uread(buf) {
                Ok((ux, n)) => (ux, n),
                Err(err) => return Err(err),
            };
            let mut x = (ux >> 1) as $signed;
            if ux & 1 != 0 {
                x = !x;
            }
            Ok((x, n))
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

const fn max_len<T>() -> usize {
    let bits = mem::size_of::<T>() * 8;
    (bits + 7 - 1) / 7
}

const fn max_last_byte<T>() -> u8 {
    let bits = mem::size_of::<T>() * 8;
    (1 << (bits % 7)) - 1
}

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
            let n = write_u8(&mut buf, x);
            assert_eq!(n, 1, "{x}");
            assert_eq!(buf, [x, 0], "{x}");
        }
    }

    macro_rules! test_max {
        ($name:ident, $write:ident, $read:ident, $type:ty) => {
            #[test]
            fn $name() {
                let mut buf = [0u8; <$type as Integer>::MAX_LEN];
                let nw = $write(&mut buf, <$type>::MAX);
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

    test_max!(test_max_i8, write_i8, read_i8, i8);
    test_max!(test_max_i16, write_i16, read_i16, i16);
    test_max!(test_max_i32, write_i32, read_i32, i32);
    test_max!(test_max_i64, write_i64, read_i64, i64);
    test_max!(test_max_i128, write_i128, read_i128, i128);

    macro_rules! test_round_trip {
        ($name:ident, $write:ident, $read:ident, $type:ty) => {
            #[test]
            fn $name() {
                for x in 0..=<$type>::MAX {
                    let mut buf = [0u8; <$type as Integer>::MAX_LEN];
                    let nw = $write(&mut buf, x);
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
