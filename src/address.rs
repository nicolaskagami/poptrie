#![allow(clippy::unusual_byte_groupings)] // Grouped 6 by 6 because that's the current STRIDE
use core::ops::{Shl, Shr};

/// A trait for types that can be used as addresses in the `Prefix`.
///
/// This is currently not sealed to allow for custom types.
/// Future versions may change this, which would be a breaking change.
///
/// - Needs to inform its bit width and a `to_u8` method that returns its 8 least significant bits.
/// - Needs to implement `rotate_right` method that rotates the key by `n` bits to the right.
///
/// # Implementation Details
///
/// The current bounds are required to guarantee performance, else there would be a more flexible
/// trait with their own bit extraction functions. This may change in the future.
///
/// # Examples
///
/// Implementing `Key` for a custom newtype:
/// ```
/// use poptrie::Key;
/// use core::ops::{Shl, Shr};
///
/// #[derive(Clone, Copy)]
/// struct MyAddr(u32);
///
/// impl Shl<u8> for MyAddr {
///     type Output = Self;
///     fn shl(self, n: u8) -> Self { MyAddr(self.0 << n) }
/// }
///
/// impl Shr<u8> for MyAddr {
///     type Output = Self;
///     fn shr(self, n: u8) -> Self { MyAddr(self.0 >> n) }
/// }
///
/// impl Key for MyAddr {
///     const BITS: u8 = 32;
///     fn to_u8(self) -> u8 { self.0 as u8 }
///     fn rotate_right(self, n: u32) -> Self { MyAddr(self.0.rotate_right(n)) }
/// }
///
/// assert_eq!(MyAddr::BITS, 32);
/// assert_eq!(MyAddr(0xdeadbeef).to_u8(), 0xef);
/// ```
pub trait Address:
    Copy + Shl<u8, Output = Self> + Shr<u8, Output = Self> + Sized
{
    /// The number of bits in the key.
    const BITS: u8;
    /// Converts the least significant bits of the key to a u8.
    fn to_u8(self) -> u8;
    /// Rotates the key to the right by `n` bits.
    fn rotate_right(self, n: u32) -> Self;
}

impl Address for u32 {
    const BITS: u8 = 32;
    #[inline(always)]
    fn to_u8(self) -> u8 {
        self as u8
    }

    #[inline(always)]
    fn rotate_right(self, n: u32) -> Self {
        self.rotate_right(n)
    }
}

impl Address for u128 {
    const BITS: u8 = 128;
    #[inline(always)]
    fn to_u8(self) -> u8 {
        self as u8
    }

    #[inline(always)]
    fn rotate_right(self, n: u32) -> Self {
        self.rotate_right(n)
    }
}

/// Extract `len` bits from `key`, starting from `offset` bits from the most
/// significant bit. Bit position is exact (msb aligned) and zero-padded to the right.
/// - `len` must be at most 8 since where returning a `u8`.
///``` text
/// MSB |------------------------key-------------------------| LSB
///     |------ offset ------|----- len ----|---remaining----|
///                           ^^^^^^^^^^^^^^
///                           extracted bits
///```
/// If `len` + `offset` > A::BITS, the extraction will be zero-padded from the right:
///``` text
/// MSB |------------------------key-------------------------| LSB
///     |---------------- offset -----------------|----- len ----|
///                                               |^^^^^^^^^^0000|
///                                                extracted bits
///```
#[inline(always)]
pub(crate) fn extract_bits<A>(address: A, offset: u8, len: u8) -> u8
where
    A: Address,
{
    (address.rotate_right((A::BITS - offset).wrapping_sub(len) as u32)).to_u8()
        & ((1u16 << len) - 1) as u8
}

/// Extracts `len` bits from `key`, starting from `offset` bits from the most
/// significant bit. Significant bits are lsb-aligned and zero-padded to the left.
/// - `len` must be at most 8 since where returning a `u8`.
///
/// ``` text
/// MSB |------------------------key-------------------------| LSB
///     |------ offset ------|----- len ----|---remaining----|
///                           ^^^^^^^^^^^^^^
///                           extracted bits
///```
/// If `len` + `offset` > `A::BITS`, the extraction will be saturated:
///
/// ``` text
/// MSB |------------------------key-------------------------| LSB
///     |---------------- offset -----------------|----- len ----|
///                                           |0000^^^^^^^^^^|
///                                            extracted bits
///```
#[inline(always)]
pub(crate) fn extract_bits_saturated<A>(address: A, offset: u8, len: u8) -> u8
where
    A: Address,
{
    // TODO: Check if mask version is faster
    let remaining = u8::saturating_sub(A::BITS - offset, len);
    if remaining + offset == A::BITS {
        return 0;
    }
    (address << offset >> (remaining + offset)).to_u8()
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
        assert_eq!(extract_bits_saturated(key, 30, 6), 1);
        let key: u32 = 0b000001_000001_000001_000001_000001_01;
        assert_eq!(extract_bits_saturated(key, 30, 6), 1);
    }

    #[test]
    fn test_msb_alignement() {
        let key: u32 = 0b000000_000000_000000_000000_000000_01;
        assert_eq!(extract_bits(key, 30, 6), 0b0001_0000);
        let key: u32 = 0b000001_000001_000001_000001_000001_01;
        assert_eq!(extract_bits(key, 30, 6), 0b0001_0000);
        assert_eq!(extract_bits(key, 0, 6), 0b0000_0001);
    }
}
