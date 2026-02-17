//! # poptrie
//!
//! A Poptrie is a data structure for efficient longest-prefix matching. It's similar to a tree bitmap, but keeps nodes in a single array.
//! # Implementation Details
//! - Pure Rust, `no_std` implementation, requiring `alloc`.
//! - No external dependencies.
//! - Not using Direct Pointing (section 3.4 of the paper).
//! - Not using buddy memory allocation.
//! - Not using incremental update (section 3.5 of the paper).
//! - Not using an auxiliary radix tree.
//! - Using an original algorithm for storing prefixes that saves space and insertion time.
//! - Using an original algorithm for keeping and updating default values.
// TODO: make generic over IPv4 and IPv6
// TODO: make stride generic
// TODO: implement longer strides (CP-trie)
// TODO: implement direct pointing (generic)
// TODO: newtypes for dealing with bitmaps? Always one base/offset, one index and ids
#![no_std]

extern crate alloc;

mod bitmap;
pub mod key;

use alloc::vec;
use alloc::vec::Vec;
use bitmap::*;
use core::cmp::min;
use core::marker::PhantomData;
use key::*;

#[derive(Debug, Clone)]
struct Node<T: Clone> {
    #[cfg(test)]
    debug_prefix: Vec<NodeId>,

    /// Bitmap of local nodes
    node_bitmap: Bitmap<NodeId>,

    /// Bitmap of local prefixes
    leaf_bitmap: Bitmap<LeafId>,

    /// Offset of the first node pointed by this node
    node_base: u32,

    /// Offset of the first leaf pointed by this node
    leaf_base: u32,

    /// The default value for this node
    default_value: Option<T>,
}

impl<T: Clone> Node<T> {
    fn new(
        #[cfg(test)] debug_prefix: Vec<NodeId>,
        node_base: u32,
        leaf_base: u32,
        default_value: Option<T>,
    ) -> Self {
        Node {
            #[cfg(test)]
            debug_prefix,
            node_bitmap: Bitmap::new(),
            leaf_bitmap: Bitmap::new(),
            node_base,
            leaf_base,
            default_value,
        }
    }
}

/// The maximum number of bits we can consume from the prefix at a time.
///
/// This is 6 because the 2^6 = 64, which is the biggest size for which a native popcount instruction exists.
const STRIDE: u8 = 6;
// TODO: generify for u128
pub struct Poptrie<K, T>
where
    K: Key,
    T: Clone,
{
    nodes: Vec<Node<T>>,
    leaves: Vec<T>,
    _marker: PhantomData<fn(K)>,
}

// TODO: generify for u128

impl<K, V> Poptrie<K, V>
where
    K: Key,
    V: Clone,
{
    pub fn new() -> Self {
        Poptrie::<K, V> {
            // Starting with an empty root node
            nodes: vec![Node::new(
                #[cfg(test)]
                Vec::new(),
                1,
                0,
                None,
            )],
            leaves: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// Insert a value into the trie associated with the given prefix.
    pub fn insert(&mut self, key: K, key_length: u8, value: V) {
        assert!(key_length <= K::BITS);
        let mut key_offset = 0;
        // First node is root
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];

        // Check if it's in the correct depth
        // We MUST use '>=' here to ensure that full strides always direct towards inner nodes.
        // This is what allows leaves to only encode up to 2^STRIDE entries, with our special representation.
        while key_length >= key_offset + STRIDE {
            let local_id = NodeId::new(extract_bits(key, key_offset, STRIDE));
            // Check if there's already one with `local_id`
            let leaf_base = parent_node.leaf_base;
            let node_base = parent_node.node_base;

            // Check if there's already a node with `local_id`
            let node_index = parent_node.node_bitmap.bitmap_index(local_id);
            // If there's no node with `local_id`, insert one
            if !parent_node.node_bitmap.contains(local_id) {
                // We never look for leaves with full strides, so we start with its parent here.
                let leaf_id = LeafId::new(local_id, STRIDE).parent();

                // Setting the default value for the new node if there's a leaf that encompasses it
                // Important not to propagate defaults down when inserting because we aren't updating them.
                let parent_default = parent_node
                    .leaf_bitmap
                    .find_leaf_lpm(leaf_id)
                    .map(|leaf_index| {
                        self.leaves[(leaf_base + leaf_index) as usize].clone()
                    });

                // Calculate the next base
                let (next_node_base, next_leaf_base) =
                    self.find_next_base((node_base + node_index) as usize);

                // Getting the leaf end of the last one
                self.nodes.insert(
                    (node_base + node_index) as usize,
                    Node::new(
                        #[cfg(test)]
                        [parent_node.debug_prefix.as_slice(), &[local_id]]
                            .concat(),
                        next_node_base,
                        next_leaf_base,
                        parent_default,
                    ),
                );

                // Set the node bitmap for the new node
                self.nodes[parent_node_index].node_bitmap.set(local_id);

                // TODO: improve this updating (could be lazy)
                // Increment every single node after parent_node_index
                for i in parent_node_index + 1..self.nodes.len() {
                    self.nodes[i].node_base += 1;
                }
            }

            // Now this node is the next parent node
            parent_node_index = (node_base + node_index) as usize;
            parent_node = &self.nodes[parent_node_index];

            // Advance the key offset
            key_offset += STRIDE;
        }

        // Can't consume a whole STRIDE, so we handle the remainder.
        let remaining_length = key_length - key_offset;
        let node_id =
            NodeId::new(extract_bits(key, key_offset, remaining_length));
        let leaf_id = LeafId::new(node_id, remaining_length);

        // TODO: Keep only indices in leaves
        let leaf_base = self.nodes[parent_node_index].leaf_base;
        let leaf_index = parent_node.leaf_bitmap.bitmap_index(leaf_id);
        // Check if there is a leaf with the key
        if !parent_node.leaf_bitmap.contains(leaf_id) {
            // Create a new leaf node
            self.leaves.insert((leaf_base + leaf_index) as usize, value);

            // Update offsets after the index
            // Now we can insert leaves - It's relatively slow having to shift everything
            for i in parent_node_index + 1..self.nodes.len() {
                self.nodes[i].leaf_base += 1;
            }

            // Set the leaf
            self.nodes[parent_node_index].leaf_bitmap.set(leaf_id);
        } else {
            // Just overwrite the existing leaf
            self.leaves[(leaf_base + leaf_index) as usize] = value;
        }

        // Update the defaults for children
        self.update_children_defaults(parent_node_index, leaf_base, leaf_index);
    }

    /// Lookup a key in the trie, performing longest-prefix match.
    pub fn lookup(&self, key: K) -> Option<V> {
        let mut key_offset = 0;
        // First node is root
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];
        let mut default = parent_node.default_value.clone();
        let mut local_id = NodeId::new(extract_bits(key, key_offset, STRIDE));

        // Should try internal nodes first, apparently. Shouldn't be a problem considering our default implementation.
        while parent_node.node_bitmap.contains(local_id) {
            // If there's a valid internal node, traverse it
            let node_base = parent_node.node_base;
            let node_offset = parent_node.node_bitmap.bitmap_index(local_id);

            // Update the parent node
            parent_node_index = (node_base + node_offset) as usize;
            parent_node = &self.nodes[parent_node_index];

            // Keep track of the latest valid default value
            if parent_node.default_value.is_some() {
                default = parent_node.default_value.clone();
            }

            // Update key offset and local ID
            key_offset += STRIDE;
            local_id = NodeId::new(extract_bits(key, key_offset, STRIDE));
        }

        // (space and insert optimization) Check leaf at local_id and its parent prefixes
        // We start by calculating the prefix index - can be improved
        let remaining_length = min(STRIDE, K::BITS - key_offset);
        // We never look for leaves with full strides, so we start with its parent if its FULL.
        let local_prefix_id = if remaining_length == STRIDE {
            LeafId::new(local_id, remaining_length).parent()
        } else {
            LeafId::new(local_id, remaining_length)
        };

        // Check leaves for receding prefixes
        if let Some(leaf_index) =
            parent_node.leaf_bitmap.find_leaf_lpm(local_prefix_id)
        {
            let leaf_base = parent_node.leaf_base;
            return Some(
                self.leaves[(leaf_base + leaf_index) as usize].clone(),
            );
        }
        default
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

    /// Update the children defaults for a given parent node index.
    fn update_children_defaults(
        &mut self,
        parent_node_index: usize,
        leaf_base: u32,
        leaf_index: u32,
    ) {
        let base_node_offset = self.nodes[parent_node_index].node_base;
        // For every child node
        for id in 0..64 {
            let node_id = NodeId::new(id);
            // If it exists
            if self.nodes[parent_node_index].node_bitmap.contains(node_id) {
                // Check if there is a leaf node in this parent node that would be more specific to this key
                // We check for leaves on the parent, which can be of at most STRIDE - 1 length.
                let local_leaf_id = LeafId::new(node_id, STRIDE).parent();
                let local_node_offset = self.nodes[parent_node_index]
                    .node_bitmap
                    .bitmap_index(node_id);
                if self.nodes[parent_node_index]
                    .leaf_bitmap
                    .find_leaf_lpm(local_leaf_id)
                    .is_some_and(|id| id == leaf_index)
                {
                    let local_default =
                        self.leaves[(leaf_base + leaf_index) as usize].clone();
                    // Set default
                    self.nodes
                        [(base_node_offset + local_node_offset) as usize]
                        .default_value = Some(local_default);
                };
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
    trie.insert(0b000001_000001_000001_000001_000000_00, 25, 0);
    trie.insert(0b000001_000001_000001_000001_000001_01, 32, 1);
    assert_eq!(
        trie.lookup(0b000001_000001_000001_000001_000001_00),
        Some(0)
    );
    assert_eq!(
        trie.lookup(0b000001_000001_000001_000001_000001_01),
        Some(1)
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
