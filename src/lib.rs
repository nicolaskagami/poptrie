//! # poptrie
//!
//! A Poptrie is a data structure for efficient longest-prefix matching. It's similar to a tree bitmap, but keeps nodes in a single array.
//! # Implementation Details
//! - Pure Rust, `no_std` implementation, requiring `alloc`.
//! - No external dependencies.
//! - Using leafvec optimization (section 3.3 of the paper).
//! - Not using Direct Pointing (section 3.4 of the paper).
//! - Not using buddy memory allocation.
//! - Not using incremental update (section 3.5 of the paper).
//! - Not using an auxiliary radix tree.
//! - Using an original algorithm for storing prefixes that saves space and insertion time.
//! - Using an original algorithm for keeping and updating default values.
// TODO: make stride generic
// TODO: implement longer strides (CP-trie)
// TODO: implement direct pointing (generic)
// TODO: newtypes for dealing with bitmaps? Always one base/offset, one index and ids

#![no_std]

extern crate alloc;

mod bitmap;
pub mod key;
mod value_index;

use alloc::collections::btree_map::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use bitmap::*;
use core::marker::PhantomData;
use key::*;

use crate::value_index::ValueIndex;

#[derive(Debug, Clone)]
struct Node {
    #[cfg(test)]
    debug_prefix: Vec<StrideId>,

    /// Bitmap of local nodes
    node_bitmap: Bitmap<StrideId>,

    /// Bitmap of local prefixes
    leaf_bitmap: Bitmap<StrideId>,

    /// Offset of the first node pointed by this node
    node_base: u32,

    /// Offset of the first leaf pointed by this node
    leaf_base: u32,
}

impl Node {
    fn new(
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
}

/// The maximum number of bits we can consume from the prefix at a time.
///
/// This is 6 because the 2^6 = 64, which is the biggest size for which a native popcount instruction exists.
const STRIDE: u8 = 6;

/// A compressed prefix tree optimized for fast longest prefix match (LPM) lookups.
///
/// # Type Parameters
///
/// * `K` - The key type (e.g., `u32` for IPv4, `u128` for IPv6)
/// * `T` - The value type associated with each prefix
///
/// # Examples
///
/// ```
/// use poptrie::Poptrie;
///
/// // Create a routing table for IPv4 addresses
/// let mut trie = Poptrie::<u32, &str>::new();
///
/// // Insert prefixes with their associated values
/// trie.insert(u32::from_be_bytes([192, 168, 0, 0]), 16, "192.168.0.0/16");
/// trie.insert(u32::from_be_bytes([192, 168, 1, 0]), 24, "192.168.1.0/24");
/// trie.insert(u32::from_be_bytes([10, 0, 0, 0]),8, "10.0.0.0/8");
///
/// // Perform longest prefix match lookups
/// assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 1, 5])), Some("192.168.1.0/24"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 2, 5])), Some("192.168.0.0/16"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 2, 3])), Some("10.0.0.0/8"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([8, 8, 8, 8])), None);
/// ```
pub struct Poptrie<K, V>
where
    K: Key,
    V: Clone,
{
    /// The internal nodes of the trie.
    nodes: Vec<Node>,

    /// The leaves of the trie, pointing to indices in the values vector.
    leaves: Vec<ValueIndex>,

    /// The values associated with the prefixes.
    values: Vec<V>,

    /// References for leaves, only used when editing the trie.
    reference: Vec<BTreeMap<PrefixId, ValueIndex>>,

    /// The marker for `K`.
    _marker: PhantomData<fn(K)>,
}

impl<K, V> Poptrie<K, V>
where
    K: Key,
    V: Clone + Default,
{
    pub fn new() -> Self {
        let mut root_node = Node::new(
            #[cfg(test)]
            Vec::new(),
            1,
            0,
        );
        // Register the default value bit
        root_node.leaf_bitmap.set(StrideId(0));
        Poptrie::<K, V> {
            values: Vec::new(),
            nodes: vec![root_node], // Start with a root node
            reference: vec![BTreeMap::new()], // Root's reference
            leaves: vec![ValueIndex::NONE], // Global default value index
            _marker: PhantomData,
        }
    }

    /// Insert a value into the trie associated with the given prefix.
    pub fn insert(&mut self, key: K, key_length: u8, value: V) {
        assert!(key_length <= K::BITS);
        // Store the value in the values vector and get its index
        self.values.push(value);
        let current_value_index =
            ValueIndex::new((self.values.len() - 1) as u32);

        // Keep track of the default value
        let mut default_value_index = ValueIndex::NONE;

        // Keep track of where we are in the key
        let mut key_offset = 0;

        // First node is root
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];

        // Check if it's in the correct depth
        // We MUST use '>=' here to ensure that full strides always direct towards inner nodes.
        while key_length >= key_offset + STRIDE {
            let local_id = StrideId::from_key(key, key_offset, STRIDE);

            // Calculate the full node index
            let full_node_index = (parent_node.node_base
                + parent_node.node_bitmap.bitmap_index(local_id))
                as usize;

            // Find the default from the parent
            let prefix_id = PrefixId::new(local_id.0, STRIDE).parent();
            if let Some(default_index) =
                find_leaf_lpm(&self.reference[parent_node_index], prefix_id)
            {
                default_value_index = default_index;
            }

            // Check if there's already a node with `local_id`
            if !parent_node.node_bitmap.contains(local_id) {
                // If there's no node with `local_id`, insert one

                // Calculate the next bases
                let (next_node_base, next_leaf_base) =
                    self.find_next_base(full_node_index);

                self.nodes.insert(
                    full_node_index,
                    Node::new(
                        #[cfg(test)]
                        [parent_node.debug_prefix.as_slice(), &[local_id]]
                            .concat(),
                        next_node_base,
                        next_leaf_base,
                    ),
                );

                // Set the node bitmap for the new node
                self.nodes[parent_node_index].node_bitmap.set(local_id);

                // Increment every single node after parent_node_index
                for i in parent_node_index + 1..self.nodes.len() {
                    self.nodes[i].node_base += 1;
                }

                // Also insert into reference
                self.reference.insert(full_node_index, BTreeMap::new());

                // Insert the default leaf, always at the base, representing the full range
                self.leaves
                    .insert(next_leaf_base as usize, default_value_index);

                // Update offsets after the index
                // Now we can insert leaves - It's relatively slow having to shift everything
                for i in full_node_index + 1..self.nodes.len() {
                    self.nodes[i].leaf_base += 1;
                }

                // Set the default leaf at 0
                self.nodes[full_node_index].leaf_bitmap.set(StrideId(0));
            }

            // Now this node is the next parent node
            parent_node_index = full_node_index;
            parent_node = &self.nodes[parent_node_index];

            // Advance the key offset
            key_offset += STRIDE;
        }

        // Can't consume a whole STRIDE, so we handle the remainder.
        let remaining_length = key_length - key_offset;

        let prefix_id = PrefixId::from_key(key, key_offset, remaining_length);

        // Store the value index for that prefix chunk
        self.reference[parent_node_index]
            .insert(prefix_id, current_value_index);

        // Update the defaults for children
        if self.calculate_leaf_ranges(parent_node_index, default_value_index) {
            self.update_children(parent_node_index, default_value_index);
        }
    }

    /// Lookup a key in the trie, performing longest-prefix match.
    pub fn lookup(&self, key: K) -> Option<V> {
        let mut key_offset = 0;
        // First node is root
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];

        let mut local_id = StrideId::from_key(key, key_offset, STRIDE);

        // Should try internal nodes first, apparently. Shouldn't be a problem considering our default implementation.
        while parent_node.node_bitmap.contains(local_id) {
            // If there's a valid internal node, traverse it
            let node_base = parent_node.node_base;
            let node_offset = parent_node.node_bitmap.bitmap_index(local_id);

            // Update the parent node
            parent_node_index = (node_base + node_offset) as usize;
            parent_node = &self.nodes[parent_node_index];

            // Update key offset and local ID
            key_offset += STRIDE;
            local_id = StrideId::from_key(key, key_offset, STRIDE);
        }

        // There will always be at least a 0th leaf (e.g. with the default)
        let leaf_index = parent_node.leaf_bitmap.leafvec_index(local_id);

        let leaf_base = parent_node.leaf_base;
        let value_index = self.leaves[(leaf_base + leaf_index) as usize];

        value_index.get().map(|i| self.values[i as usize].clone())
    }

    /// Find the next base node and leaf node index for a given parent node index.
    ///
    /// Used for inserting a new node while keeping the order of nodes.
    /// It will get the latest descendant node that's before the new node.
    fn find_next_base(&self, next_node_index: usize) -> (u32, u32) {
        // SAFETY: We start with a root node at 0
        let last_node = &self.nodes[next_node_index - 1];
        let next_leaf_base =
            last_node.leaf_base + last_node.leaf_bitmap.pop_count();
        let next_node_base =
            last_node.node_base + last_node.node_bitmap.pop_count();

        (next_node_base, next_leaf_base)
    }

    /// Calculate the leaf ranges so they can be read with `leafvec_index`.
    ///
    /// We'll need to recalculate the whole leaf bitmap, since the default may require multiple ranges.
    /// Example: default is 0/0 but we have a 0001/4, meaning we need:
    /// - bit 0: default (0000/4)
    /// - bit 1: other (0001/4)
    /// - bit 2: default (rest)
    fn calculate_leaf_ranges(
        &mut self,
        node_index: usize,
        default_value_index: ValueIndex,
    ) -> bool {
        let mut changed = false;
        let mut leaves_inserted = 0;
        let leaf_base = self.nodes[node_index].leaf_base as usize;

        // We go through every possible index and correct it.
        // Small optimization:Since leaves have at most STRIDE-1 length, we can skip half and calculate a simpler `PrefixId`.
        for prefix in 0..(1 << (STRIDE - 1)) {
            // Get the correct value index
            let correct_value = find_leaf_lpm(
                &self.reference[node_index],
                PrefixId::new(prefix, STRIDE - 1),
            )
            .unwrap_or(default_value_index);

            let leaf_id = StrideId(prefix << 1);

            // This index is where the leafvec optimization is telling us to look
            let leafvec_index =
                self.nodes[node_index].leaf_bitmap.leafvec_index(leaf_id);

            let current_value = self.leaves[leaf_base + leafvec_index as usize];

            // If it's not correct, update it
            if current_value != correct_value {
                changed = true;

                // The bitmap index is where is should be read if it exists or inserted if it doesn't
                let leaf_bitmap_index = leaf_base
                    + self.nodes[node_index].leaf_bitmap.bitmap_index(leaf_id)
                        as usize;

                // Now we either create a new entry or update the existing one
                if !self.nodes[node_index].leaf_bitmap.contains(leaf_id) {
                    leaves_inserted += 1;
                    self.leaves.insert(leaf_bitmap_index, correct_value);
                    self.nodes[node_index].leaf_bitmap.set(leaf_id);
                } else {
                    self.leaves[leaf_bitmap_index] = correct_value;
                }
            }
        }

        // Update leaf bases
        for i in node_index + 1..self.nodes.len() {
            self.nodes[i].leaf_base += leaves_inserted;
        }

        changed
    }

    /// Update the children defaults for a given parent node index.
    fn update_children(
        &mut self,
        parent_node_index: usize,
        parent_default: ValueIndex,
    ) {
        let node_base = self.nodes[parent_node_index].node_base as usize;

        // Check every possible
        for prefix in 0..(1 << (STRIDE)) {
            let child_id = StrideId(prefix);

            if self.nodes[parent_node_index].node_bitmap.contains(child_id) {
                let child_node_index = self.nodes[parent_node_index]
                    .node_bitmap
                    .bitmap_index(child_id);
                let full_child_node_index =
                    node_base + child_node_index as usize;

                // Calculate the default for the child
                let prefix_id = PrefixId::new(child_id.0, STRIDE).parent();
                let default_value = find_leaf_lpm(
                    &self.reference[parent_node_index],
                    prefix_id,
                )
                .unwrap_or(parent_default);

                // If something changed, update its children
                if self
                    .calculate_leaf_ranges(full_child_node_index, default_value)
                {
                    self.update_children(full_child_node_index, default_value);
                }
            }
        }
    }
}

#[test]
fn test_find_leaf() {
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(u32::from_be_bytes([192, 168, 0, 0]), 30, 0);
    trie.insert(u32::from_be_bytes([192, 168, 0, 1]), 32, 1);
    trie.insert(u32::from_be_bytes([192, 168, 0, 2]), 32, 2);

    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 0])), Some(0));
    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 1])), Some(1));
    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 2])), Some(2));
    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 3])), Some(0));
}

#[test]
fn one_level_before() {
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(0b000001_000001_000001_000001_000000_00, 25, 1);
    trie.insert(0b000001_000001_000001_000001_000011_01, 32, 2);
    assert_eq!(
        trie.lookup(0b000001_000001_000001_000001_000001_00),
        Some(1)
    );
    assert_eq!(
        trie.lookup(0b000001_000001_000001_000001_000011_01),
        Some(2)
    );
}

#[test]
fn base_default() {
    // Levels 1 and 2
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(0b000001_000000_000000_000000_000000_00, 6, 0);
    trie.insert(0b000000_000000_000000_000000_000000_00, 12, 1);
    assert_eq!(
        trie.lookup(0b000001_000000_000000_000000_000000_00),
        Some(0)
    );
    // Levels 2 and 3
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(0b000000_110000_000000_000000_000000_00, 12, 0);
    trie.insert(0b000000_000000_000000_000000_000000_00, 18, 1);
    assert_eq!(
        trie.lookup(0b000000_110000_000000_000000_000000_00),
        Some(0)
    );
    // Levels 1 and 2 (non-full length)
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(0b001100_000000_000000_000000_000000_00, 10, 0);
    trie.insert(0b000000_000000_000000_000000_000000_00, 1, 1);
    assert_eq!(
        trie.lookup(0b001100_000100_000000_000000_000000_00),
        Some(1)
    );
}

#[test]
fn default_overwrite() {
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(0b000000_000000_000000_000000_000000_00, 0, 0);
    trie.insert(0b000001_000001_000000_000000_000000_00, 15, 2);
    trie.insert(0b000000_000000_000000_000000_000000_00, 0, 1);
    assert_eq!(
        trie.lookup(0b000001_000001_001000_000000_000000_00),
        Some(1)
    );
}

#[test]
fn simple() {
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(0b000000_000000_000000_000000_000000_00, 1, 1);
    assert_eq!(
        trie.lookup(0b000000_000000_001000_000000_000000_00),
        Some(1)
    );
}

#[test]
fn simple2() {
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(0b000000_000000_000000_000000_000000_00, 0, 1);
    trie.insert(0b000001_000000_000000_000000_000000_00, 7, 2);
    trie.insert(0b000001_100000_000000_000000_000000_00, 13, 3);
    assert_eq!(
        trie.lookup(0b000001_100000_100000_000000_000000_00),
        Some(1)
    );
}

#[test]
fn simple3() {
    let mut trie = Poptrie::<u32, u32>::new();
    trie.insert(0b000001_100001_000000_000000_000000_00, 13, 13);
    trie.insert(0b000001_000000_000000_000000_000000_00, 12, 12);
    trie.insert(0b000001_000000_000000_000000_000000_00, 7, 7);
    assert_eq!(trie.lookup(0b000001_100001_100000_000000_000000_00), None,);
}
