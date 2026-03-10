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
mod prefix;
mod value_index;

pub use iter::{IntoIter, Iter, IterMut, Keys, Values, ValuesMut};
pub use key::Key;
pub use prefix::Prefix;

use alloc::collections::btree_map::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use bitmap::*;
use core::cmp::min;
use value_index::ValueIndex;

/// The maximum number of bits we can consume from the prefix at a time.
///
/// This is 6 because the 2^6 = 64, which is the biggest size for which a native popcount
/// instruction exists.
const STRIDE: u8 = 6;

/// A tuple representing a prefix entry in the trie, consisting of a prefix and value index.
type Entry<P> = (P, ValueIndex);

/// A compressed prefix tree optimized for fast longest prefix match (LPM) lookups.
///
/// # Type Parameters
///
/// * `P`: [`Prefix`] - The prefix type (e.g. `(u32, u8)` for IPv4 or `(u128, u8)` for IPv6),
/// * `V` - The value type associated with each prefix.
///
/// # Examples
///
/// ```
/// use poptrie::Poptrie;
///
/// // Create a routing table for IPv4 addresses
/// let mut trie = Poptrie::<(u32, u8), &str>::new();
///
/// trie.insert((u32::from_be_bytes([192, 168, 0, 0]), 16), "192.168.0.0/16");
/// trie.insert((u32::from_be_bytes([192, 168, 1, 0]), 24), "192.168.1.0/24");
/// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8),    "10.0.0.0/8");
///
/// // Perform longest prefix match lookups
/// assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 1, 5])), Some(&"192.168.1.0/24"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 2, 5])), Some(&"192.168.0.0/16"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 2, 3])), Some(&"10.0.0.0/8"));
/// assert_eq!(trie.lookup(u32::from_be_bytes([8, 8, 8, 8])), None);
/// ```
#[derive(Debug, Clone, Default)]
pub struct Poptrie<P, V>
where
    P: Prefix,
{
    /// The internal nodes of the trie.
    nodes: Vec<Node>,

    /// The leaves of the trie, pointing to indices in the values vector.
    leaves: Vec<ValueIndex>,

    /// The values associated with the prefixes.
    values: Vec<V>,

    /// The entries associated with each node.
    entries: Vec<BTreeMap<PrefixId, Entry<P>>>,
}

impl<P, V> Poptrie<P, V>
where
    P: Prefix,
{
    /// Construct a new, empty poptrie.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let trie = Poptrie::<(u32, u8), ()>::new();
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
        Poptrie::<P, V> {
            values: Vec::new(),
            nodes: vec![root_node], // Start with a root node
            entries: vec![BTreeMap::new()], // Root's entries
            leaves: vec![ValueIndex::NONE], // Global default value index
        }
    }

    /// Insert a value into the trie associated with the given prefix,
    /// returning the previous value if one existed.
    ///
    /// # Panics
    ///
    /// Panics if `prefix.prefix_length() > P::ADDRESS::BITS`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    ///
    /// // Insert a /8 prefix
    /// assert_eq!(trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), "10.0.0.0/8"), None);
    ///
    /// // Insert a more specific /24 prefix
    /// assert_eq!(trie.insert((u32::from_be_bytes([10, 1, 2, 0]), 24), "10.1.2.0/24"), None);
    ///
    /// // Replacing an existing prefix returns the old value
    /// assert_eq!(trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), "new"), Some("10.0.0.0/8"));
    ///
    /// // Insert a default route (0-length prefix matches everything)
    /// assert_eq!(trie.insert((0u32, 0), "default"), None);
    /// ```
    pub fn insert(&mut self, prefix: P, mut value: V) -> Option<V> {
        let key = prefix.address();
        let key_length = prefix.prefix_length();

        assert!(key_length <= P::ADDRESS::BITS);

        let mut default_value_index = ValueIndex::NONE;
        let mut key_offset = 0;

        // First node is root
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];

        // Check if it's in the correct depth
        // We MUST use '>=' here to ensure that full strides always direct towards inner nodes.
        while key_length >= key_offset + STRIDE {
            let local_id = StrideId::from_key(key, key_offset, STRIDE);
            let full_node_index = parent_node.get_child_index(local_id);

            // Find the default from the parent
            default_value_index = self.get_default(parent_node_index, local_id);

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

                // Also insert into entries
                self.entries.insert(full_node_index, BTreeMap::new());

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

        // If an entry already exists, reuse it and return the old value
        let old_value = if let Some(idx) = self.entries[parent_node_index]
            .get(&prefix_id)
            .and_then(|(_, v)| v.get())
        {
            core::mem::swap(&mut value, &mut self.values[idx]);
            Some(value)
        } else {
            self.values.push(value);
            let current_value_index =
                ValueIndex::new((self.values.len() - 1) as u32);
            self.entries[parent_node_index]
                .insert(prefix_id, (prefix, current_value_index));
            None
        };

        // Update the defaults for children
        self.calculate_leaf_ranges(parent_node_index, default_value_index);

        old_value
    }

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
    pub fn lookup(&self, key: P::ADDRESS) -> Option<&V> {
        lookup_inner(&self.nodes, &self.leaves, key).map(|i| &self.values[i])
    }

    /// Returns `true` if the trie contains an entry for the exact prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
    ///
    /// assert!(trie.contains_key((u32::from_be_bytes([10, 0, 0, 0]), 8)));
    /// assert!(!trie.contains_key((u32::from_be_bytes([10, 0, 0, 0]), 7)));
    /// assert!(!trie.contains_key((u32::from_be_bytes([192, 168, 0, 0]), 16)));
    /// ```
    pub fn contains_key(&self, prefix: P) -> bool {
        let (parent_node, prefix_id, _) = self.find_parent_node(prefix);
        self.entries[parent_node].contains_key(&prefix_id)
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

    /// Returns a reference to the value associated with the exact prefix, or
    /// `None` if it was not present.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
    ///
    /// assert_eq!(trie.get((u32::from_be_bytes([10, 0, 0, 0]), 8)),  Some(&8));
    /// assert_eq!(trie.get((u32::from_be_bytes([10, 0, 0, 0]), 16)), None);
    /// ```
    pub fn get(&self, prefix: P) -> Option<&V> {
        let (parent_node, prefix_id, _) = self.find_parent_node(prefix);
        self.entries[parent_node]
            .get(&prefix_id)
            .and_then(|(_, vi)| vi.get().map(|i| &self.values[i]))
    }

    /// Returns a mutable reference to the value associated with the exact
    /// prefix, or `None` if it was not present.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 1u32);
    ///
    /// if let Some(v) = trie.get_mut((u32::from_be_bytes([10, 0, 0, 0]), 8)) {
    ///     *v *= 10;
    /// }
    ///
    /// assert_eq!(trie.get((u32::from_be_bytes([10, 0, 0, 0]), 8)), Some(&10));
    /// ```
    pub fn get_mut(&mut self, prefix: P) -> Option<&mut V> {
        let (parent_node, prefix_id, _) = self.find_parent_node(prefix);
        self.entries[parent_node]
            .get(&prefix_id)
            .and_then(|(_, vi)| vi.get())
            .map(|i| &mut self.values[i])
    }

    /// Returns an iterator over the prefixes of the trie, in lexicographic order of `(prefix_length, address)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8),  8u32);
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);
    ///
    /// let keys: Vec<_> = trie.keys().collect();
    /// assert_eq!(keys, [
    ///     &(u32::from_be_bytes([10, 0, 0, 0]), 8),
    ///     &(u32::from_be_bytes([10, 1, 0, 0]), 16),
    /// ]);
    /// ```
    pub fn keys(&self) -> Keys<'_, P, V> {
        Keys(self.iter())
    }

    /// Returns an iterator over the values of the trie, in lexicographic
    /// order of `(prefix_length, address)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8),  8u32);
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);
    ///
    /// let values: Vec<_> = trie.values().collect();
    /// assert_eq!(values, [&8, &16]);
    /// ```
    pub fn values(&self) -> Values<'_, P, V> {
        Values(self.iter())
    }

    /// Returns a mutable iterator over the values of the trie.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8),  1u32);
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 2u32);
    ///
    /// for v in trie.values_mut() { *v *= 10; }
    ///
    /// assert_eq!(trie.get((u32::from_be_bytes([10, 0, 0, 0]), 8)),  Some(&10));
    /// assert_eq!(trie.get((u32::from_be_bytes([10, 1, 0, 0]), 16)), Some(&20));
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, P, V> {
        ValuesMut(self.iter_mut())
    }

    /// Retains only the entries for which the predicate returns `true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8),  8u32);
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);
    /// trie.insert((u32::from_be_bytes([10, 1, 2, 0]), 24), 24u32);
    ///
    /// trie.retain(|_, v| *v <= 16);
    ///
    /// assert_eq!(trie.len(), 2);
    /// assert!(trie.contains_key((u32::from_be_bytes([10, 0, 0, 0]), 8)));
    /// assert!(trie.contains_key((u32::from_be_bytes([10, 1, 0, 0]), 16)));
    /// assert!(!trie.contains_key((u32::from_be_bytes([10, 1, 2, 0]), 24)));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&P, &mut V) -> bool,
    {
        let to_remove: Vec<_> = self
            .iter_mut()
            .filter_map(|(p, v)| if !f(p, v) { Some(*p) } else { None })
            .collect();

        for prefix in to_remove {
            self.remove(prefix);
        }
    }

    /// Removes and returns the value associated with the exact prefix, or
    /// `None` if it was not present.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8),  8u32);
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);
    ///
    /// // Remove the /16 prefix
    /// assert_eq!(trie.remove((u32::from_be_bytes([10, 1, 0, 0]), 16)), Some(16));
    ///
    /// // Addresses previously matched by /16 now fall back to /8
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 2, 3])), Some(&8));
    ///
    /// // Removing a prefix that doesn't exist returns `None`
    /// assert!(!trie.contains_key((u32::from_be_bytes([10, 1, 0, 0]), 16)));
    /// ```
    pub fn remove(&mut self, prefix: P) -> Option<V> {
        let (parent_node, prefix_id, default_value_index) =
            self.find_parent_node(prefix);

        self.entries[parent_node].remove(&prefix_id).map(|(_, v)| {
            // Update the leaf ranges
            self.calculate_leaf_ranges(parent_node, default_value_index);

            // Update the value indices in all the leaves and entries
            for higher_v in self
                .leaves
                .iter_mut()
                .chain(
                    self.entries
                        .iter_mut()
                        .flat_map(|s| s.values_mut().map(|(_, vi)| vi)),
                )
                .filter(|higher_v| **higher_v > v)
            {
                higher_v.decrement();
            }

            // SAFETY: The value is guaranteed to exist because it was just removed from the
            // entry map.
            self.values.remove(v.get().unwrap())
        })
    }

    /// Find the final parent node and the `PrefixId` of the given key.
    fn find_parent_node(&self, prefix: P) -> (usize, PrefixId, ValueIndex) {
        let key = prefix.address();
        let key_length = prefix.prefix_length();
        let mut key_offset = 0;
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];
        let mut default_value_index = ValueIndex::NONE;

        while key_length >= key_offset + STRIDE {
            let local_id = StrideId::from_key(key, key_offset, STRIDE);
            default_value_index = self.get_default(parent_node_index, local_id);

            if !parent_node.node_bitmap.contains(local_id) {
                break;
            }

            parent_node_index = parent_node.get_child_index(local_id);
            parent_node = &self.nodes[parent_node_index];

            key_offset += STRIDE;
        }

        let remaining_length = min(key_length - key_offset, STRIDE - 1);
        let prefix_id = PrefixId::from_key(key, key_offset, remaining_length);

        (parent_node_index, prefix_id, default_value_index)
    }

    /// Find the next base node and leaf node index for a given parent node index.
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
    /// Propagates the changes to its children. The process is slightly
    /// involved as more specific ranges may cut the representational space.
    ///
    /// Example: default is 0/0 but we have a 0001/4, meaning we need:
    /// - bit 0: default (0000/4)
    /// - bit 1: other (0001/4)
    /// - bit 2: default (rest)
    fn calculate_leaf_ranges(
        &mut self,
        node_index: usize,
        default_value_index: ValueIndex,
    ) {
        // Currently using a not-in-place version
        let leaf_base = self.nodes[node_index].leaf_base as usize;

        // Let's keep track of children's original defaults:
        let ids = self.nodes[node_index].node_bitmap.bit_positions();
        let original_defaults: Vec<_> = ids
            .iter()
            .map(|p| self.get_default(node_index, StrideId(*p)))
            .collect();

        let (new_bitmap, new_leaves) = build_leaf_ranges(
            self.entries[node_index].iter().map(|(&pid, &(_, vi))| (pid, vi)),
            default_value_index,
        );

        let old_end = if node_index < self.nodes.len() - 1 {
            self.nodes[node_index + 1].leaf_base as usize
        } else {
            self.leaves.len()
        };
        let balance =
            new_leaves.len() as isize - (old_end - leaf_base) as isize;

        self.nodes[node_index].leaf_bitmap = new_bitmap;
        self.leaves.splice(leaf_base..old_end, new_leaves);

        for node in &mut self.nodes[node_index + 1..] {
            node.leaf_base = (node.leaf_base as isize + balance) as u32;
        }

        // Check if position changed and update leaves accordingly
        for (i, id) in ids.iter().enumerate() {
            let new_default = self.get_default(node_index, StrideId(*id));
            if original_defaults[i] != new_default {
                let child_index = self.nodes[node_index].node_base as usize + i;
                self.calculate_leaf_ranges(child_index, new_default);
            }
        }
    }

    /// Gets the default for a node given its parent index and the stride id
    /// that points to it.
    fn get_default(
        &self,
        parent_node_index: usize,
        node_stride_id: StrideId,
    ) -> ValueIndex {
        let parent_node = &self.nodes[parent_node_index];
        let leaf_bitmap_index = parent_node.leaf_base
            + self.nodes[parent_node_index]
                .leaf_bitmap
                .leafvec_index(node_stride_id);
        self.leaves[leaf_bitmap_index as usize]
    }

    /// Very similar to `build_leaf_ranges`, but used only for bulk insertion.
    /// Assumptions:
    /// - The node has no leaves.
    /// - It won't need to fix leaf bases.
    /// - It won't need to propagate changes.
    fn build_leaf_ranges_bulk_insert(
        &mut self,
        node_index: usize,
        default_value_index: ValueIndex,
    ) {
        let leaf_base = self.nodes[node_index].leaf_base as usize;
        let leaf_bitmap = &mut self.nodes[node_index].leaf_bitmap;

        let mut entries = self.entries[node_index].iter().peekable();
        let default = entries
            .peek()
            .take_if(|(p, _)| p.prefix_length() == 0)
            .map(|(_, (_, v))| *v)
            .unwrap_or(default_value_index);

        self.leaves.insert(leaf_base, default);
        leaf_bitmap.set(StrideId(0));

        for (prefix_id, (_, value)) in entries {
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
}

/// An internal node in the trie
#[derive(Debug, Clone, Default)]
struct Node {
    /// Debug field for keeping track of stride ascendancy.
    #[cfg(test)]
    debug_prefix: Vec<StrideId>,

    /// Bitmap of local nodes
    node_bitmap: Bitmap,

    /// Bitmap of local prefixes
    leaf_bitmap: Bitmap,

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

    /// Returns the index of the child node pointed by `local_id`.
    #[inline(always)]
    fn get_child_index(&self, local_id: StrideId) -> usize {
        (self.node_base + self.node_bitmap.bitmap_index(local_id)) as usize
    }
}

// Idea: try to iterate over entries, adding in increasing order of prefix id
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
// This means that:
// - next = base + cover
// - next = (prefix + 1) << (STRIDE - len)
// TODO: Analyze performance characteristics of doing it in-band:
// - For `Poptrie::insert`, multiple leaves may have to added, where each insert pushes the following leaves
// - We could not always shrink, trading a little cache locality for insertion speed.
fn build_leaf_ranges(
    entries: impl Iterator<Item = (PrefixId, ValueIndex)>,
    default_value_index: ValueIndex,
) -> (Bitmap, Vec<ValueIndex>) {
    let mut leaf_bitmap = Bitmap::new();

    let mut entries = entries.peekable();
    let default = entries
        .peek()
        .take_if(|(p, _)| p.prefix_length() == 0)
        .map(|(_, v)| *v)
        .unwrap_or(default_value_index);

    let mut leaves = vec![default];
    leaf_bitmap.set(StrideId(0));

    for (prefix_id, value) in entries {
        let (prefix, len) = prefix_id.components();
        let leaf_id = prefix_id.stride_id();
        let leafvec_index = leaf_bitmap.leafvec_index(leaf_id) as usize;
        let initial_value = leaves[leafvec_index];

        let leaf_bitmap_index = leaf_bitmap.bitmap_index(leaf_id) as usize;

        // Insert new leaf or rewrite a possible terminator
        if !leaf_bitmap.contains(leaf_id) {
            leaves.insert(leaf_bitmap_index, value);
            leaf_bitmap.set(leaf_id);
        } else {
            leaves[leaf_bitmap_index] = value;
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

/// Monomorphized to just `K` has a decent performance impact.
fn lookup_inner<K: Key>(
    nodes: &[Node],
    leaves: &[ValueIndex],
    key: K,
) -> Option<usize> {
    let mut key_offset = 0;
    // First node is root
    let mut parent_node_index = 0;
    let mut parent_node = &nodes[parent_node_index];

    let mut local_id = StrideId::from_key(key, key_offset, STRIDE);

    // Should always try internal nodes first.
    while parent_node.node_bitmap.contains(local_id) {
        // If there's a valid internal node, traverse it
        parent_node_index = parent_node.get_child_index(local_id);
        parent_node = &nodes[parent_node_index];

        // Update key offset and local ID
        key_offset += STRIDE;
        local_id = StrideId::from_key(key, key_offset, STRIDE);
    }

    // There will always be at least a 0th leaf (e.g. with the default)
    let leaf_index = parent_node.leaf_bitmap.leafvec_index(local_id);

    let leaf_base = parent_node.leaf_base;
    let value_index = leaves[(leaf_base + leaf_index) as usize];

    value_index.get()
}
