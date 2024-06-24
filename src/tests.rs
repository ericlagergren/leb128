#![cfg(test)]

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

/// Exhaustive test for a `u32`-based `encoded_len!`.
#[test]
#[cfg(not(any(miri, debug_assertions)))]
fn test_encoded_len() {
    const fn size_varint(mut x: u32) -> usize {
        let mut s = 1;
        while x >= 128 {
            s += 1;
            x >>= 7;
        }
        s
    }
    for i in 0..u32::MAX {
        let got = encoded_len(&i);
        assert_eq!(got, size_varint(i), "#{i}");
    }
}

macro_rules! test_max {
    ($name:ident, $write:ident, $read:ident, $type:ty) => {
        #[test]
        fn $name() {
            let mut buf = [0u8; <$type as Varint>::MAX_LEN];
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
                let mut buf = [0u8; <$type as Sealed>::MAX_LEN];
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
