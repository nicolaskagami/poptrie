//! # poptrie
//!
//! A pure Rust implementation of [Poptrie](https://dl.acm.org/doi/abs/10.1145/2829988.2787474),
//! a data structure for efficient longest-prefix matching (LPM) lookups.
//!
//! Poptrie uses bitmaps combined with the popcount instruction to achieve fast IP routing
//! table lookups with high cache locality. During lookup, the key is consumed in the biggest
//! step that can be represented in a bitmap for which the native popcount instruction exists
//! (i.e. 6-bit steps in a 64-bit bitmap), similarly to how a tree-bitmap works, but with a
//! more contiguous use of memory, trading insertion speed for cache locality.
//!
//! This is particularly useful for IP forwarding tables, where the longest-prefix matching is a
//! common operation and insertions are comparatively rare.
//!
//! # Reference
//! Asai, Hirochika, and Yasuhiro Ohara. **[Poptrie: A Compressed Trie with Population Count for
//! Fast and Scalable Software IP Routing Table Lookup](https://doi.org/10.1145/2829988.2787474)**
//! ACM SIGCOMM Computer Communication Review 45.4 (2015): 57-70.
use core::marker::PhantomData;

pub use crate::prefix::Prefix;

use alloc::vec::Vec;
use crate::bitmap::*;
use crate::value_index::ValueIndex;

/// The core of a compressed prefix tree optimized for fast longest prefix match (LPM) lookups.
///
/// # Type Parameters
///
/// * `P`: [`Prefix`] - The prefix type (e.g. `(u32, u8)` for IPv4 or `(u128, u8)` for IPv6),
/// * `V` - The value type associated with each prefix.
#[derive(Debug, Clone, Default)]
pub struct PoptrieCore<P, V>
where
    P: Prefix,
{
    /// The internal nodes of the trie.
    pub(crate) nodes: Vec<Node>,

    /// The leaves of the trie, pointing to indices in the values vector.
    pub(crate) leaves: Vec<ValueIndex>,

    /// The values associated with the prefixes.
    pub(crate) values: Vec<V>,

    // Pins the prefix type
    pub(crate) _phantom: PhantomData<P>,
}

impl<P, V> PoptrieCore<P, V>
where
    P: Prefix,
{
     /// Lookup an address in the trie, performing longest-prefix match.
    ///
    /// Returns `None` if no prefix matches the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    ///
    /// // No match without a default route
    /// assert_eq!(trie.lookup(u32::from_be_bytes([8, 8, 8, 8])), None);
    ///
    /// trie.insert((0u32, 0), "default");
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), "10/8");
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), "10.1/16");
    ///
    /// // Longest prefix match: 10.1.2.3 matches 10.1/16
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 2, 3])), Some(&"10.1/16"));
    ///
    /// // Falls back to 10/8
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 2, 0, 0])), Some(&"10/8"));
    ///
    /// // Falls back to default
    /// assert_eq!(trie.lookup(u32::from_be_bytes([8, 8, 8, 8])), Some(&"default"));
    /// ```
    pub fn lookup<A: Into<P::ADDRESS>>(&self, address: A) -> Option<&V> {
        let address = address.into();

        let mut offset = 0;
        // First node is root
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];

        let mut local_id = StrideId::from_address(address, offset, crate::STRIDE);

        // Should always try internal nodes first.
        while parent_node.node_bitmap.contains(local_id) {
            // If there's a valid internal node, traverse it
            parent_node_index = parent_node.get_child_index(local_id);
            parent_node = &self.nodes[parent_node_index];

            // Update key offset and local ID
            offset += crate::STRIDE;
            local_id = StrideId::from_address(address, offset, crate::STRIDE);
        }

        // There will always be at least a 0th leaf (e.g. with the default)
        let leaf_index = parent_node.leaf_bitmap.leafvec_index(local_id);

        let leaf_base = parent_node.leaf_base;
        let value_index = self.leaves[(leaf_base + leaf_index) as usize];

        value_index.get().map(|i| &self.values[i])
    }

    /// Returns the number of entries in the trie.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::<(u32, u8), u32>::new();
    /// assert_eq!(trie.len(), 0);
    ///
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
    /// assert_eq!(trie.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Returns `true` if the trie contains no prefixes.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::<(u32, u8), u32>::new();
    /// assert!(trie.is_empty());
    ///
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
    /// assert!(!trie.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

/// An internal node in the trie
#[derive(Debug, Clone, Default)]
pub(crate) struct Node {
    /// Debug field for keeping track of stride ascendancy.
    #[cfg(test)]
    pub(crate) debug_prefix: Vec<StrideId>,

    /// Bitmap of local nodes
    pub(crate) node_bitmap: Bitmap,

    /// Bitmap of local prefixes
    pub(crate) leaf_bitmap: Bitmap,

    /// Offset of the first node pointed by this node
    pub(crate) node_base: u32,

    /// Offset of the first leaf pointed by this node
    pub(crate) leaf_base: u32,
}

impl Node {
    pub(crate) fn new(
        #[cfg(test)] debug_prefix: Vec<StrideId>,
        node_base: u32,
        leaf_base: u32,
    ) -> Self {
        Node {
            #[cfg(test)]
            debug_prefix,
            node_bitmap: Bitmap::new(),
            leaf_bitmap: Bitmap::new(),
            node_base,
            leaf_base,
        }
    }

    /// Returns the index of the child node pointed by `local_id`.
    #[inline(always)]
    pub(crate) fn get_child_index(&self, local_id: StrideId) -> usize {
        (self.node_base + self.node_bitmap.bitmap_index(local_id)) as usize
    }
}
