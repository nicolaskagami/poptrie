/// Extract `len` bits from `key`, starting from `offset` bits from the most
/// significant bit.
///
///  MSB |---------- offset -----------|----- len -----|---remaining---| LSB
///                                     ^^^^^^^^^^^^^^^
///                                     extracted  bits
///
/// If `len` + `offset` > 32, the extraction will be saturated. (?)
pub(crate) fn extract_bits(key: u32, offset: u8, len: u8) -> u32 {
    // TODO: Check if mask version is faster
    let remaining = u8::saturating_sub(32u8 - offset, len); // `offset` should never reach 32. `len` could and should saturate
    if remaining + offset == 32 {
        return 0;
    }
    key << offset >> (remaining + offset)
}

// Idea: u128 bitfield to 1-1 associate any leaf prefix
// Prefix representation:
// (XXXXXX_XX)(prefix length 0) -> 0
// (0XXXXX_XX)(prefix length 1) -> 1
// (1XXXXX_XX)(prefix length 1) -> 2
// ...
// But we actually have the id, which is represented as
// (XXXXXX_XX) -> prefix 0000 0000, len 0
// (0XXXXX_XX) -> prefix 0000 0000, len 1
// (1XXXXX_XX) -> prefix 0000 0001, len 1
// We can get the the bit index like this:
// (prefix, len) -> 2^len + prefix
//
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct LeafId(u8);
pub(crate) fn bitmap_id_prefix_u128(prefix: u8, len: u8) -> LeafId {
    LeafId((1u8 << len) - 1 + prefix)
}

pub(crate) fn bitmap_contains(bitmap: u64, id: u8) -> bool {
    bitmap & (1 << id) != 0
}

pub(crate) fn bitmap_contains_u128(bitmap: u128, id: LeafId) -> bool {
    bitmap & (1 << id.0) != 0
}

pub(crate) fn bitmap_set(bitmap: &mut u64, id: u8) {
    *bitmap |= 1 << id;
}

// TODO: Id should be enforced as a type
pub(crate) fn bitmap_set_u128(bitmap: &mut u128, id: LeafId) {
    *bitmap |= 1 << id.0;
}

#[allow(dead_code)]
pub(crate) fn clear_lsb(key: &mut u8, len: u8) {
    *key &= 0xFF << len;
}

/// Returns the number of 1s in bitmap before or equal to `id`
//
// TODO: Consider a way to not have to -1 some places
pub(crate) fn bitmap_index(bitmap: u64, id: u8) -> u32 {
    (bitmap << (63u8 - id)).count_ones()
}

pub(crate) fn bitmap_index_u128(bitmap: u128, id: LeafId) -> u32 {
    (bitmap << (127u8 - id.0)).count_ones()
}

/// Returns leaf index for the prefix
pub(crate) fn find_leaf_lpm(
    leaf_bitmap: u128,
    mut local_id: LeafId,
) -> Option<u32> {
    loop {
        if bitmap_contains_u128(leaf_bitmap, local_id) {
            break Some(bitmap_index_u128(leaf_bitmap, local_id) - 1);
        }
        if local_id.0 == 0 {
            break None;
        };
        // Subtract 1 and divide by 2
        local_id.0 = (local_id.0 - 1) >> 1;
    }
}

#[cfg(test)]
mod tests {
    use core::u64;

    use super::*;

    #[test]
    fn test_extraction() {
        let key = 0b11111111_01010101_11110000_11001100;
        assert_eq!(extract_bits(key, 0, 8), 0b11111111);
        assert_eq!(extract_bits(key, 8, 8), 0b01010101);
        assert_eq!(extract_bits(key, 16, 8), 0b11110000);
        assert_eq!(extract_bits(key, 24, 8), 0b11001100);
    }

    #[test]
    fn bitmap_index_test() {
        assert_eq!(bitmap_index(0, 0), 0);
        assert_eq!(bitmap_index(0, 63), 0);

        assert_eq!(bitmap_index(1, 0), 1);
        assert_eq!(bitmap_index(1, 1), 1);
        assert_eq!(bitmap_index(1, 63), 1);

        assert_eq!(bitmap_index(32, 4), 0);
        assert_eq!(bitmap_index(32, 5), 1);
        assert_eq!(bitmap_index(32, 63), 1);

        assert_eq!(bitmap_index(1u64.rotate_right(1), 0), 0);
        assert_eq!(bitmap_index(1u64.rotate_right(1), 62), 0);
        assert_eq!(bitmap_index(1u64.rotate_right(1), 63), 1);

        assert_eq!(bitmap_index(u64::MAX, 63), 64);
    }

    #[test]
    fn bitmap_id_prefix_test() {
        assert_eq!(bitmap_id_prefix_u128(0, 0), LeafId(0));
        assert_eq!(bitmap_id_prefix_u128(0, 1), LeafId(1));
        assert_eq!(bitmap_id_prefix_u128(1, 1), LeafId(2));
    }

    #[test]
    fn test_saturated_extraction() {
        let key = 0b000000_000000_000000_000000_000000_01;
        assert_eq!(extract_bits(key, 30, 6), 1);
        let key = 0b000001_000001_000001_000001_000001_01;
        assert_eq!(extract_bits(key, 30, 6), 1);
    }
}
