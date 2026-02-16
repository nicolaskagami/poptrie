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

/// A unique identifier for a leaf node in the IP trie.
///
/// The ID is a mapping of the last segment of the prefix, i.e. the last "stride", including the valid length.
/// It's calculated as follows: `f(prefix, len) = 2^len + prefix`.
/// This is so that the parent prefix can be directly calculated as: `parent` = `(leaf_id - 1) >> 1`, just like in a heap.
/// - Valid ranges are `0..2^(MAX_LEN + 1)`.
/// - `prefix` is the numerical representation of the last valid segment of the prefix, not a mask.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct LeafId(u8);
impl LeafId {
    /// Creates a new `LeafId` from a prefix and length.
    pub fn new(prefix: NodeId, len: u8) -> Self {
        LeafId((1u8 << len) - 1 + prefix.0)
    }

    /// Returns the parent `LeafId`.
    pub(crate) fn parent(&self) -> Self {
        LeafId((self.0 - 1) >> 1)
    }
}

/// Bitmap for storing leaf IDs.
///
/// It's currently a `u128` because we need to store up to `2^(MAX_LEN + 1)` leaf IDs and we're currently using a `STRIDE` of `6`.
/// This is so we can store the significant length along with the prefix of the leaf even when it's not the full stride.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct LeafBitmap(u128);
impl LeafBitmap {
    /// Creates a new unpopulated `LeafBitmap`.
    pub fn new() -> Self {
        LeafBitmap(0)
    }

    /// Returns the internal index of the given leaf ID.
    pub(crate) fn bitmap_index(&self, id: LeafId) -> u32 {
        if id.0 == 0 {
            0
        } else {
            (self.0 << (128u8 - id.0)).count_ones()
        }
    }

    /// Returns internal index for the longest prefix match of a leaf ID.
    pub(crate) fn find_leaf_lpm(&self, mut local_id: LeafId) -> Option<u32> {
        while !self.contains(local_id) {
            if local_id.0 == 0 {
                return None;
            }
            local_id = local_id.parent();
        }
        Some(self.bitmap_index(local_id))
    }

    /// Returns true if the bitmap contains the given leaf ID.
    pub(crate) fn contains(&self, id: LeafId) -> bool {
        self.0 & (1 << id.0) != 0
    }

    /// Sets the given leaf ID in the bitmap.
    pub(crate) fn set(&mut self, id: LeafId) {
        self.0 |= 1 << id.0;
    }

    /// Returns the number of leaves in the bitmap.
    pub(crate) fn pop_count(&self) -> u32 {
        self.0.count_ones()
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct NodeId(u8);
impl NodeId {
    pub(crate) fn new(id: u8) -> NodeId {
        NodeId(id)
    }
}

//TODO: Consider simplifying Bitmap usage into a trait/generic struct
#[derive(Debug, Clone, Copy)]
pub(crate) struct NodeBitmap(u64);
impl NodeBitmap {
    pub(crate) fn new() -> NodeBitmap {
        NodeBitmap(0)
    }

    /// Returns the internal index of the given node ID.
    pub(crate) fn bitmap_index(&self, id: NodeId) -> u32 {
        if id.0 == 0 {
            0
        } else {
            (self.0 << (64u8 - id.0)).count_ones()
        }
    }

    /// Returns true if the bitmap contains the given node ID.
    pub(crate) fn contains(&self, id: NodeId) -> bool {
        self.0 & (1 << id.0) != 0
    }

    /// Sets the given node ID in the bitmap.
    pub(crate) fn set(&mut self, id: NodeId) {
        self.0 |= 1 << id.0;
    }

    /// Returns the number of nodes in the bitmap.
    pub(crate) fn pop_count(&self) -> u32 {
        self.0.count_ones()
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
        let zero = NodeBitmap(0);
        assert_eq!(zero.bitmap_index(NodeId(0)), 0);
        assert_eq!(zero.bitmap_index(NodeId(63)), 0);

        let one = NodeBitmap(1);
        assert_eq!(one.bitmap_index(NodeId(0)), 0);
        assert_eq!(one.bitmap_index(NodeId(1)), 1);
        assert_eq!(one.bitmap_index(NodeId(63)), 1);

        let thirty_two = NodeBitmap(32);
        assert_eq!(thirty_two.bitmap_index(NodeId(5)), 0);
        assert_eq!(thirty_two.bitmap_index(NodeId(6)), 1);
        assert_eq!(thirty_two.bitmap_index(NodeId(63)), 1);

        let max = NodeBitmap(u64::MAX);
        assert_eq!(max.bitmap_index(NodeId(63)), 63);
    }

    #[test]
    fn bitmap_id_prefix_test() {
        assert_eq!(LeafId::new(NodeId(0), 0), LeafId(0));
        assert_eq!(LeafId::new(NodeId(0), 1), LeafId(1));
        assert_eq!(LeafId::new(NodeId(1), 1), LeafId(2));
    }

    #[test]
    fn test_saturated_extraction() {
        let key = 0b000000_000000_000000_000000_000000_01;
        assert_eq!(extract_bits(key, 30, 6), 1);
        let key = 0b000001_000001_000001_000001_000001_01;
        assert_eq!(extract_bits(key, 30, 6), 1);
    }
}
