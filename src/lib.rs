//! # poptrie
//!
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
//! This is particularly useful for IP routing tables, where the longest-prefix matching is a
//! common operation and insertions are comparatively rare.
//!
//! # Reference
//! Asai, Hirochika, and Yasuhiro Ohara. **[Poptrie: A Compressed Trie with Population Count for Fast and Scalable Software IP Routing Table Lookup](https://doi.org/10.1145/2829988.2787474)** ACM SIGCOMM Computer Communication Review 45.4 (2015): 57-70.

#![no_std]
extern crate alloc;

mod bitmap;
mod iter;
mod key;
mod value_index;

pub use key::Key;

use alloc::collections::btree_map::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use bitmap::*;
use core::cmp::min;
use core::marker::PhantomData;
use value_index::ValueIndex;

/// The maximum number of bits we can consume from the prefix at a time.
///
/// This is 6 because the 2^6 = 64, which is the biggest size for which a native popcount
/// instruction exists.
const STRIDE: u8 = 6;

/// A compressed prefix tree optimized for fast longest prefix match (LPM) lookups.
///
/// # Type Parameters
///
/// * `K`: [`Key`] - The key type (e.g., `u32` for IPv4, `u128` for IPv6)
/// * `V` - The value type associated with each prefix
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
/// trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, "10.0.0.0/8");
///
/// // Perform longest prefix match lookups
/// assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 1, 5])), Some(&"192.168.1.0/24"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 2, 5])), Some(&"192.168.0.0/16"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 2, 3])), Some(&"10.0.0.0/8"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([8, 8, 8, 8])), None);
/// ```
#[derive(Debug, Clone, Default)]
pub struct Poptrie<K, V>
where
    K: Key,
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
{
    /// Construct a new, empty poptrie.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let trie = Poptrie::<u32, ()>::new();
    /// ```
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
    ///
    /// # Panics
    ///
    /// Panics if `key_length > K::BITS`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    ///
    /// // Insert a /8 prefix
    /// trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, "10.0.0.0/8");
    ///
    /// // Insert a more specific /24 prefix
    /// trie.insert(u32::from_be_bytes([10, 1, 2, 0]), 24, "10.1.2.0/24");
    ///
    /// // Insert a default route (0-length prefix matches everything)
    /// trie.insert(0u32, 0, "default");
    /// ```
    pub fn insert(&mut self, key: K, key_length: u8, value: V) {
        assert!(key_length <= K::BITS);
        // Store the value in the values vector and get its index
        self.values.push(value);
        let current_value_index =
            ValueIndex::new((self.values.len() - 1) as u32);

        let mut default_value_index = ValueIndex::NONE;
        let mut key_offset = 0;

        // First node is root
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];

        // Check if it's in the correct depth
        // We MUST use '>=' here to ensure that full strides always direct towards inner nodes.
        while key_length >= key_offset + STRIDE {
            let local_id = StrideId::from_key(key, key_offset, STRIDE);

            let full_node_index = (parent_node.node_base
                + parent_node.node_bitmap.bitmap_index(local_id))
                as usize;

            // Find the default from the parent
            let leaf_bitmap_index = (parent_node.leaf_base
                + parent_node.leaf_bitmap.leafvec_index(local_id))
                as usize;
            default_value_index = self.leaves[leaf_bitmap_index];

            // Check if there's already a node with `local_id`
            if !parent_node.node_bitmap.contains(local_id) {
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

            parent_node_index = full_node_index;
            parent_node = &self.nodes[parent_node_index];

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
            self.update_children(parent_node_index);
        }
    }

    /// Lookup a key in the trie, performing longest-prefix match.
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
    /// trie.insert(0u32, 0, "default");
    /// trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, "10/8");
    /// trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, "10.1/16");
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
    pub fn lookup(&self, key: K) -> Option<&V> {
        let mut key_offset = 0;
        // First node is root
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];

        let mut local_id = StrideId::from_key(key, key_offset, STRIDE);

        // Should always try internal nodes first.
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

        value_index.get().map(|i| &self.values[i])
    }

    /// Returns `true` if the trie contains an entry for the exact prefix
    /// `(key, key_length)`.
    ///
    /// Note that this checks for an exact prefix match, not a longest-prefix
    /// match. A key that would resolve via [`lookup`](Self::lookup) may still
    /// return `false` here if it was never explicitly inserted with that length.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 8u32);
    ///
    /// // Exact prefix is present
    /// assert!(trie.contains_key(u32::from_be_bytes([10, 0, 0, 0]), 8));
    ///
    /// // Different length — not present, even though lookup would succeed
    /// assert!(!trie.contains_key(u32::from_be_bytes([10, 0, 0, 0]), 7));
    /// assert!(!trie.contains_key(u32::from_be_bytes([10, 0, 0, 0]), 9));
    ///
    /// // Completely absent prefix
    /// assert!(!trie.contains_key(u32::from_be_bytes([192, 168, 0, 0]), 16));
    /// ```
    pub fn contains_key(&self, key: K, key_length: u8) -> bool {
        // Find the final parent node and prefix id
        let (parent_node, prefix_id, _) =
            self.find_parent_node(key, key_length);

        self.reference[parent_node].contains_key(&prefix_id)
    }

    /// Removes and returns the value associated with the exact prefix
    /// `(key, key_length)`, or `None` if it was not present.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 8u32);
    /// trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 16u32);
    ///
    /// // Remove the /16 prefix
    /// assert_eq!(trie.remove(u32::from_be_bytes([10, 1, 0, 0]), 16), Some(16));
    ///
    /// // Addresses previously matched by /16 now fall back to /8
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 2, 3])), Some(&8));
    ///
    /// // Removing a prefix that doesn't exist returns None
    /// assert!(!trie.contains_key(u32::from_be_bytes([10, 1, 0, 0]), 16));
    /// ```
    pub fn remove(&mut self, key: K, key_length: u8) -> Option<V> {
        // Find the final parent node and prefix id
        let (parent_node, prefix_id, default_value_index) =
            self.find_parent_node(key, key_length);

        self.reference[parent_node].remove(&prefix_id).map(|v| {
            // Update the leaf ranges
            if self.calculate_leaf_ranges(parent_node, default_value_index) {
                self.update_children(parent_node);
            }

            // Update the value indices in all the leaves and references
            for higher_v in self
                .leaves
                .iter_mut()
                .chain(self.reference.iter_mut().flat_map(|s| s.values_mut()))
                .filter(|higher_v| **higher_v > v)
            {
                higher_v.decrement();
            }

            // SAFETY: The value is guaranteed to exist because it was just removed from the
            // reference map.
            self.values.remove(v.get().unwrap())
        })
    }

    /// Find the final parent node and the `PrefixId` of the given key.
    fn find_parent_node(
        &self,
        key: K,
        key_length: u8,
    ) -> (usize, PrefixId, ValueIndex) {
        // Traverse the trie similarly to a insert but check the reference
        let mut key_offset = 0;
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];
        let mut default_value_index = ValueIndex::NONE;

        while key_length >= key_offset + STRIDE {
            let local_id = StrideId::from_key(key, key_offset, STRIDE);

            let leaf_bitmap_index = (parent_node.leaf_base
                + parent_node.leaf_bitmap.leafvec_index(local_id))
                as usize;
            default_value_index = self.leaves[leaf_bitmap_index];

            // Check if there's already a node with `local_id`
            if !parent_node.node_bitmap.contains(local_id) {
                // If there's no node with `local_id`, break out
                break;
            }

            // Calculate the full node index
            parent_node_index = (parent_node.node_base
                + parent_node.node_bitmap.bitmap_index(local_id))
                as usize;

            // Now this node is the next parent node
            parent_node = &self.nodes[parent_node_index];

            // Advance the key offset
            key_offset += STRIDE;
        }

        let remaining_length = min(key_length - key_offset, STRIDE - 1);
        let prefix_id = PrefixId::from_key(key, key_offset, remaining_length);

        (parent_node_index, prefix_id, default_value_index)
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
    /// We'll need to recalculate the whole leaf bitmap, since the default may require multiple
    /// ranges.
    /// Example: default is 0/0 but we have a 0001/4, meaning we need:
    /// - bit 0: default (0000/4)
    /// - bit 1: other (0001/4)
    /// - bit 2: default (rest)
    fn calculate_leaf_ranges(
        &mut self,
        node_index: usize,
        default_value_index: ValueIndex,
    ) -> bool {
        // Currently using a not-in-place version
        let leaf_base = self.nodes[node_index].leaf_base as usize;
        let (new_bitmap, new_leaves) =
            build_leaf_ranges(&self.reference[node_index], default_value_index);

        let old_end = if node_index < self.nodes.len() - 1 {
            self.nodes[node_index + 1].leaf_base as usize
        } else {
            self.leaves.len()
        };
        let balance =
            new_leaves.len() as isize - (old_end - leaf_base) as isize;

        let bitmap_changed = new_bitmap != self.nodes[node_index].leaf_bitmap;
        if bitmap_changed {
            self.nodes[node_index].leaf_bitmap = new_bitmap;
        }

        let leaves_changed = self.leaves[leaf_base..old_end] != new_leaves[..];
        self.leaves.splice(leaf_base..old_end, new_leaves);

        for node in &mut self.nodes[node_index + 1..] {
            node.leaf_base = (node.leaf_base as isize + balance) as u32;
        }

        bitmap_changed || leaves_changed
    }

    /// Very similar to `build_leaf_ranges`, but used only for bulk insertion.
    /// Presumes that there aren't leaves after it.
    fn build_leaf_ranges_bulk_insert(
        &mut self,
        node_index: usize,
        default_value_index: ValueIndex,
    ) {
        let leaf_base = self.nodes[node_index].leaf_base as usize;
        let leaf_bitmap = &mut self.nodes[node_index].leaf_bitmap;

        let mut references = self.reference[node_index].iter().peekable();
        let default = if let Some((PrefixId(0), _)) = references.peek() {
            *references.next().unwrap().1
        } else {
            default_value_index
        };

        self.leaves.insert(leaf_base, default);
        leaf_bitmap.set(StrideId(0));

        for (prefix_id, value) in references {
            let (prefix, len) = prefix_id.components();
            let leaf_id = prefix_id.stride_id();
            let leafvec_index = leaf_bitmap.leafvec_index(leaf_id);
            let initial_value = self.leaves[leaf_base + leafvec_index as usize];

            let leaf_bitmap_index =
                leaf_base + leaf_bitmap.bitmap_index(leaf_id) as usize;
            if !leaf_bitmap.contains(leaf_id) {
                self.leaves.insert(leaf_bitmap_index, *value);
                leaf_bitmap.set(leaf_id);
            } else {
                self.leaves[leaf_bitmap_index] = *value;
            }

            let next_id = StrideId((prefix + 1) << (STRIDE - len));
            if next_id.0 != (1 << STRIDE) && !leaf_bitmap.contains(next_id) {
                let next_bitmap_index =
                    leaf_base + leaf_bitmap.bitmap_index(next_id) as usize;
                self.leaves.insert(next_bitmap_index, initial_value);
                leaf_bitmap.set(next_id);
            }
        }
    }

    /// Update the children defaults for a given parent node index.
    /// Requires that the parent's leaves be up-to-date.
    fn update_children(&mut self, parent_node_index: usize) {
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
                let leaf_bitmap_index = (self.nodes[parent_node_index]
                    .leaf_base
                    + self.nodes[parent_node_index]
                        .leaf_bitmap
                        .leafvec_index(child_id))
                    as usize;
                let default_value = self.leaves[leaf_bitmap_index];

                // If something changed, update its children
                if self
                    .calculate_leaf_ranges(full_child_node_index, default_value)
                {
                    self.update_children(full_child_node_index);
                }
            }
        }
    }
}

/// An internal node in the trie
#[derive(Debug, Clone, Default)]
struct Node {
    /// Debug field for keeping track of stride ascendancy.
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

// Idea: try to iterate over reference, adding in increasing order of prefix id
// if prefix id 0 doesn't exist it will use default
// For each prefix in tree:
// - Remember the value currently assigned (with leaf id)
// - Push a leaf at the correct place
// - Push a terminating leaf wherever the range would finish
// Since prefix id starts with the smallest prefix lengths, terminator should always have the value that existed initially.
// A bit of math now:
// prefix_id | prefix/len | base | cover | next
// 0         | 0/0        | 0    | 64    | 64 (out)
// 1         | 0/1        | 0    | 32    | 32
// 2         | 1/1        | 32   | 32    | 64 (out)
// 3         | 0/2        | 0    | 16    | 16
// 4         | 1/2        | 16   | 16    | 32
// ...
// - next = base + cover
// - next = (prefix + 1) << (STRIDE - len)
// TODO: Analyze performance characteristics of doing it in-band:
// - For `Poptrie::insert`, multiple leaves may have to added, where each insert pushes the following leaves
// - We could not always shrink, trading a little cache locality for insertion speed.
fn build_leaf_ranges(
    reference: &BTreeMap<PrefixId, ValueIndex>,
    default_value_index: ValueIndex,
) -> (Bitmap<StrideId>, Vec<ValueIndex>) {
    let mut leaf_bitmap = Bitmap::new();

    // Prepare default
    let mut references = reference.iter().peekable();
    let default = if let Some((PrefixId(0), _)) = references.peek() {
        *references.next().unwrap().1
    } else {
        default_value_index
    };

    let mut leaves = vec![default];
    leaf_bitmap.set(StrideId(0));

    for (prefix_id, value) in references {
        let (prefix, len) = prefix_id.components();
        let leaf_id = prefix_id.stride_id();
        let leafvec_index = leaf_bitmap.leafvec_index(leaf_id) as usize;
        let initial_value = leaves[leafvec_index];

        // Insert new leaf or rewrite a possible terminator
        let leaf_bitmap_index = leaf_bitmap.bitmap_index(leaf_id) as usize;
        if !leaf_bitmap.contains(leaf_id) {
            leaves.insert(leaf_bitmap_index, *value);
            leaf_bitmap.set(leaf_id);
        } else {
            leaves[leaf_bitmap_index] = *value;
        }

        let next_id = StrideId((prefix + 1) << (STRIDE - len));

        // Check if we need to insert a terminator
        // We don't insert if:
        // - It's the end of representation
        // - It already exists, meaning something more relevant is already there
        if next_id.0 != (1 << STRIDE) && !leaf_bitmap.contains(next_id) {
            let next_bitmap_index = leaf_bitmap.bitmap_index(next_id) as usize;
            leaves.insert(next_bitmap_index, initial_value);
            leaf_bitmap.set(next_id);
        }
    }

    (leaf_bitmap, leaves)
}
