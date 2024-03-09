// #![cfg(feature = "std")]
// #![cfg_attr(docs, doc(cfg(feature = "std")))]

use std::io::Read;
use std::io::Result;

use crate::Integer;

/// Extends [`Read`] with methods for reading LEB128-encoded
/// integers.
pub trait ReadLeb128: Read {
    fn read_int<T: Integer>(&mut self) -> Result<T> {
        let mut buf = T::Buf::default();
        self.read_exact(&mut buf);
    }

    fn read_u8(&mut self) -> Result<u8> {
        self.read_int::<u8>()
    }

    fn read_u16(&mut self) -> Result<u16> {
        self.read_int::<u16>()
    }

    fn read_u32(&mut self) -> Result<u32> {
        self.read_int::<u32>()
    }

    fn read_u64(&mut self) -> Result<u64> {
        self.read_int::<u64>()
    }

    fn read_u128(&mut self) -> Result<u128> {
        self.read_int::<u128>()
    }
}
