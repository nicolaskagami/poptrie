use core::ops::{Shl, Shr};

/// A trait for types that can be used as keys in the poptrie.
///
/// Needs to inform its bit width and a `to_u8` method that returns its 8 least significant bits.
pub trait Key:
    Copy + Shl<u8, Output = Self> + Shr<u8, Output = Self> + Sized
{
    const BITS: u8;
    fn to_u8(self) -> u8;
}

impl Key for u32 {
    const BITS: u8 = 32;
    #[inline(always)]
    fn to_u8(self) -> u8 {
        self as u8
    }
}

impl Key for u128 {
    const BITS: u8 = 128;
    #[inline(always)]
    fn to_u8(self) -> u8 {
        self as u8
    }
}

/// Extract `len` bits from `key`, starting from `offset` bits from the most
/// significant bit.
///
///  MSB |---------- offset -----------|----- len -----|---remaining---| LSB
///                                     ^^^^^^^^^^^^^^^
///                                     extracted  bits
///
/// - If `len` + `offset` > K::BITS, the extraction will be saturated.
/// - `len` must be at most 8 since where returning a `u8`.
pub(crate) fn extract_bits<K>(key: K, offset: u8, len: u8) -> u8
where
    K: Key,
{
    // TODO: Check if mask version is faster
    let remaining = u8::saturating_sub(K::BITS - offset, len);
    if remaining + offset == K::BITS {
        return 0;
    }
    (key << offset >> (remaining + offset)).to_u8()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extraction() {
        let key: u32 = 0b11111111_01010101_11110000_11001100;
        assert_eq!(extract_bits(key, 0, 8), 0b11111111);
        assert_eq!(extract_bits(key, 8, 8), 0b01010101);
        assert_eq!(extract_bits(key, 16, 8), 0b11110000);
        assert_eq!(extract_bits(key, 24, 8), 0b11001100);
    }

    #[test]
    fn test_saturated_extraction() {
        let key: u32 = 0b000000_000000_000000_000000_000000_01;
        assert_eq!(extract_bits(key, 30, 6), 1);
        let key: u32 = 0b000001_000001_000001_000001_000001_01;
        assert_eq!(extract_bits(key, 30, 6), 1);
    }
}
