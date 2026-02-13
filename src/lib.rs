//! Poptrie implementation
// - no-std
// - generic over u32 (IPv4) and u128 (IPv6)
// - not using buddy memory allocation
// - probably not using incremental update
// TODO: implement for u32
// TODO: implement construction
// TODO: implement lookup
// TODO: make stride generic
// TODO: implement longer strides (CP-trie)
// TODO: implement direct pointing (generic)

/// Extract `len` bits from `key`, starting from `offset` bits from the most
/// significant bit.
///
///  MSB |---------- offset -----------|----- len -----|---remaining---| LSB
///                                     ^^^^^^^^^^^^^^^
///                                     extracted  bits
pub fn extract_bits(key: u32, offset: u8, len: u8) -> u32 {
    // TODO: Check if mask version is faster
    let remaining = 32 - offset - len;
    key << offset >> remaining + offset
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extraction() {
        let key = 0b11111111_01010101_11110000_11001100;
        assert_eq!(extract_bits(key, 0, 8), 0b11111111);
        assert_eq!(extract_bits(key, 8, 8), 0b01010101);
        assert_eq!(extract_bits(key, 16, 8), 0b11110000);
        assert_eq!(extract_bits(key, 24, 8), 0b11001100);
    }
}
