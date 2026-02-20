use core::marker::PhantomData;

use alloc::collections::btree_map::BTreeMap;

use crate::key::{Key, extract_bits, extract_bits_saturated};

/// A generic bitmap for storing u8 encoded ids of 0..63
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Bitmap<T>
where
    T: Copy + Into<u8>,
{
    bits: u64,
    _phantom: PhantomData<T>,
}

impl<T> Bitmap<T>
where
    T: Copy + Into<u8>,
{
    /// Creates a new unpopulated `LeafBitmap`.
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Bitmap { bits: 0u64, _phantom: PhantomData }
    }

    /// Returns the internal index of the given leaf ID.
    #[inline(always)] // Particularly effective to inline
    pub(crate) fn bitmap_index(&self, id: T) -> u32 {
        if id.into() == 0 {
            0
        } else {
            (self.bits << (64u8 - id.into())).count_ones()
        }
    }

    /// Returns true if the bitmap contains the given ID.
    #[inline(always)]
    pub(crate) fn contains(&self, id: T) -> bool {
        self.bits & (1 << id.into()) != 0
    }

    /// Sets the given ID in the bitmap.
    #[inline(always)]
    pub(crate) fn set(&mut self, id: T) {
        self.bits |= 1 << id.into();
    }

    /// Returns the number of entries in the bitmap.
    #[inline(always)]
    pub(crate) fn pop_count(&self) -> u32 {
        self.bits.count_ones()
    }
}

impl Bitmap<StrideId> {
    /// Returns the index of leaf attributed to the given `LeafId` using leafvec optimization
    // Actually slower than `bitmap_index`
    #[inline(always)] // Particularly effective to inline
    pub(crate) fn leafvec_index(&self, id: StrideId) -> u32 {
        (self.bits << (63u8 - id.0)).count_ones() - 1
    }
}

/// A unique identifier for a prefix in the poptrie.
///
/// The ID is a mapping of the last segment of the prefix, i.e. the last "stride", including the valid length.
/// It's calculated as follows: `f(prefix, len) = 2^len + prefix`.
/// This is so that the parent prefix can be directly calculated as: `parent` = `(leaf_id - 1) >> 1`, just like in a heap.
/// - Valid ranges are `0..2^(MAX_LEN + 1)`.
/// - `prefix` is the numerical representation of the last valid segment of the prefix, not a mask.
/// We don't need to set its bitmap to `u128` at the moment because we reject full STRIDEs, those should always go into their own node, even if it becomes a stride of 0.
/// This crucially halves the representational space, allowing us to use the most effective popcount implementation.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct PrefixId(u8);
impl PrefixId {
    /// Creates a new `PrefixId` from a prefix and length.
    pub(crate) fn new(prefix: u8, len: u8) -> Self {
        PrefixId((1u8 << len) - 1 + prefix)
    }

    pub(crate) fn from_key<K: Key>(key: K, key_offset: u8, stride: u8) -> Self {
        let prefix = extract_bits_saturated(key, key_offset, stride);
        PrefixId::new(prefix, stride)
    }

    /// Returns the parent `PrefixId`.
    pub(crate) fn parent(&self) -> Self {
        PrefixId((self.0 - 1) >> 1)
    }
}

/// Returns internal index for the longest prefix match of a leaf ID.
#[inline(always)]
pub(crate) fn find_leaf_lpm<T>(
    tree: &BTreeMap<PrefixId, T>,
    mut local_id: PrefixId,
) -> Option<T>
where
    T: Copy,
{
    while !tree.contains_key(&local_id) {
        if local_id.0 == 0 {
            return None;
        }
        local_id = local_id.parent();
    }
    Some(tree[&local_id])
}

/// A unique identifier for a stride in the poptrie.
#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub(crate) struct StrideId(pub(crate) u8);
impl StrideId {
    pub(crate) fn from_key<K: Key>(
        key: K,
        key_offset: u8,
        length: u8,
    ) -> StrideId {
        StrideId(extract_bits(key, key_offset, length))
    }
}

impl Into<u8> for StrideId {
    fn into(self) -> u8 {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitmap_index_test() {
        let mut bitmap = Bitmap::<u8>::new();
        assert_eq!(bitmap.bitmap_index(0), 0);
        assert_eq!(bitmap.bitmap_index(63), 0);

        bitmap.set(1);
        assert_eq!(bitmap.bitmap_index(1), 0);
        assert_eq!(bitmap.bitmap_index(2), 1);
        assert_eq!(bitmap.bitmap_index(63), 1);

        let mut thirty_two = Bitmap::<u8>::new();
        thirty_two.set(5);
        assert_eq!(thirty_two.bitmap_index(5), 0);
        assert_eq!(thirty_two.bitmap_index(6), 1);
        assert_eq!(thirty_two.bitmap_index(63), 1);

        let mut full = Bitmap::<u8>::new();
        full.bits = u64::MAX;
        assert_eq!(full.bitmap_index(63), 63);
    }

    #[test]
    fn bitmap_id_prefix_test() {
        assert_eq!(PrefixId::new(0, 0), PrefixId(0));
        assert_eq!(PrefixId::new(0, 1), PrefixId(1));
        assert_eq!(PrefixId::new(1, 1), PrefixId(2));
    }

    #[test]
    fn test_find_lpm() {
        let mut tree = BTreeMap::<PrefixId, u32>::new();
        // Insert 1/1 prefix
        tree.insert(PrefixId::new(1, 1), 1);
        // Should see itself and its descendants
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(1, 1)), Some(1));
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(2, 2)), Some(1));
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(3, 2)), Some(1));
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(4, 3)), Some(1));
        // Insert 2/2 prefix
        tree.insert(PrefixId::new(2, 2), 2);
        // Should overwrite the longer prefix
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(2, 2)), Some(2));
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(4, 3)), Some(2));
        // Other branch (3/2) should default to first
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(1, 1)), Some(1));
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(3, 2)), Some(1));
        // None should cover the 0/1
        assert_eq!(find_leaf_lpm(&tree, PrefixId::new(0, 1)), None);
    }
}
