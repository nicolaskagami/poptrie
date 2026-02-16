//! Poptrie implementation
// - no-std, (requires alloc)
// - generic over u32 (IPv4) and u128 (IPv6)
// - not using buddy memory allocation
// - probably not using incremental update
// TODO: implement for u32
// TODO: implement construction
// TODO: implement lookup
// TODO: make stride generic
// TODO: implement longer strides (CP-trie)
// TODO: implement direct pointing (generic)
// TODO: newtypes for dealing with bitmaps? Always one base/offset, one index and ids

#![no_std]
pub mod bits;

extern crate alloc;
use core::cmp::min;

use alloc::vec;
use alloc::vec::Vec;
use bits::*;

#[derive(Debug, Clone)]
struct Node<T: Clone> {
    #[cfg(test)]
    debug_prefix: Vec<u8>,

    /// Bitmap of local nodes
    node_bitmap: u64,

    /// Bitmap of local prefixes
    leaf_bitmap: LeafBitmap,
    // TODO: Consider making offsets more local so it's faster to update.
    // Cost is a few adds during traversal.
    /// Offset of the first node pointed by this node
    node_offset: u32,

    /// Offset of the first leaf pointed by this node
    leaf_offset: u32,

    /// The default value for this node
    default_value: Option<T>,
}

impl<T: Clone> Node<T> {
    fn new(
        #[cfg(test)] debug_prefix: Vec<u8>,
        node_offset: u32,
        leaf_offset: u32,
        default_value: Option<T>,
    ) -> Self {
        Node {
            #[cfg(test)]
            debug_prefix,
            node_bitmap: 0,
            leaf_bitmap: LeafBitmap::new(),
            node_offset,
            leaf_offset,
            default_value,
        }
    }
}

const STRIDE: u8 = 6;
// TODO: generify for u128
pub struct Poptrie<T: Clone> {
    nodes: Vec<Node<T>>,
    leaves: Vec<T>,
}

// TODO: generify for u128
pub struct Prefix(pub u32, pub u8);

impl<T: Clone> Poptrie<T> {
    pub fn new() -> Self {
        Poptrie {
            // Starting with an empty root node
            nodes: vec![Node::new(
                #[cfg(test)]
                Vec::new(),
                1,
                0,
                None,
            )],
            leaves: Vec::new(),
        }
    }

    // Problem: what if there is an internal node, but our best match is before it?
    // We'd either have to lookout for best matches while traversing the trie or have to insert a default for every internal node.
    // Challenge with the latter is that when inserting a new entry we need to make it default for some nodes
    // We'd need to check the leaf bitmap of the entry to see if there are
    pub fn insert(&mut self, prefix: Prefix, value: T) {
        let Prefix(key, key_length) = prefix;
        let mut key_offset = 0;
        // First node is root
        let mut parent_node_index = 0;
        // TODO: Improve borrowing around parent_node (currently cloning)
        let mut parent_node = self.nodes[parent_node_index].clone();

        // Check if it's in the correct depth
        // If we use '>', we prefer STRIDE length representations at one level earlier, else we prefer 0 length
        while key_length >= key_offset + STRIDE {
            // We may need to insert one node per depth
            // We'll need to insert if it doesn't already exist
            // If we use '>=', we need to correct for 0 remaining length
            let stride = if key_length == key_offset { 0 } else { STRIDE };
            let local_id = extract_bits(key, key_offset, stride) as u8;
            // Check if there's already one with `local_id`
            let base_leaf_offset = parent_node.leaf_offset;
            let base_node_offset = parent_node.node_offset;

            // Check if there's already a node with `local_id`
            let local_node_offset;
            // If there's no node with `local_id`, insert one
            if !bitmap_contains(parent_node.node_bitmap, local_id) {
                // This is the offset + 1, since we're adding a new one
                local_node_offset =
                    bitmap_index(parent_node.node_bitmap, local_id);
                let local_leaf_id = LeafId::new(local_id, stride);

                // TODO: Clean this up... Important not to propagate defaults down when inserting because we aren't updating them.
                let mut parent_default = None;
                // Setting the default value for the new node if there's a leaf that encompasses it
                if let Some(leaf_index) =
                    parent_node.leaf_bitmap.find_leaf_lpm(local_leaf_id)
                {
                    let leaf_default = self.leaves
                        [(base_leaf_offset + leaf_index) as usize]
                        .clone();
                    parent_default = Some(leaf_default);
                }

                // Calculate the next base
                let (next_node_base, next_leaf_base) = self.find_next_base(
                    (base_node_offset + local_node_offset) as usize,
                );

                // Getting the leaf end of the last one
                self.nodes.insert(
                    (base_node_offset + local_node_offset) as usize,
                    Node::new(
                        #[cfg(test)]
                        [parent_node.debug_prefix.as_slice(), &[local_id]]
                            .concat(),
                        next_node_base,
                        next_leaf_base,
                        parent_default.clone(),
                    ),
                );
                // Let's ensure that nodes are stored in order
                // If it inserts more nodes, all the following ones will have to be updated as well
                bitmap_set(
                    &mut self.nodes[parent_node_index].node_bitmap,
                    local_id,
                );
                // TODO: improve this updating (could be lazy)
                // Increment every single node after parent_node_index
                for i in parent_node_index + 1..self.nodes.len() {
                    self.nodes[i].node_offset += 1;
                }
            } else {
                // This is the normal offset
                local_node_offset =
                    bitmap_index(parent_node.node_bitmap, local_id) - 1;
            }
            // Now this node is the next parent node
            parent_node_index = (base_node_offset + local_node_offset) as usize;

            parent_node = self.nodes[parent_node_index].clone();

            key_offset += STRIDE;
        }

        let remaining_length = key_length - key_offset;
        let local_id = extract_bits(key, key_offset, remaining_length) as u8;
        // We don't need to clear the bits that are not used because the extraction function already does it for us.

        let leaf_id = LeafId::new(local_id, remaining_length);

        // TODO: Keep only indices in leaves
        let base_leaf_offset = self.nodes[parent_node_index].leaf_offset;
        let local_leaf_offset = parent_node.leaf_bitmap.bitmap_index(leaf_id);
        // Check if there is a leaf with the key
        if !parent_node.leaf_bitmap.contains(leaf_id) {
            // Create a new leaf node
            self.leaves
                .insert((base_leaf_offset + local_leaf_offset) as usize, value);

            // Update offsets after the index
            // Now we can insert leaves - It's relatively slow having to shift everything
            for i in parent_node_index + 1..self.nodes.len() {
                self.nodes[i].leaf_offset += 1;
            }

            // Set the leaf
            self.nodes[parent_node_index].leaf_bitmap.set(leaf_id);
        } else {
            self.leaves[(base_leaf_offset + local_leaf_offset) as usize] =
                value;
        }
        // TODO: Insert default for internal nodes
        // Careful! Check the leaf bitmap of this node to see there are more specific prefixes... let's not think about delete just yet.
        // The default will be the /0 of that stride. If it explicitly exists in that subtree we shouldn't overwrite it.
        // Else, if it was set by one of our leaves... the longest prefix needs to win.

        // For every child node
        // let i = 0; // Could sub in for local_node_offset
        let base_node_offset = self.nodes[parent_node_index].node_offset;
        // TODO: Improve this search
        for id in 0..=63 {
            // If it exists
            if bitmap_contains(parent_node.node_bitmap, id) {
                // Check if there is a leaf node in this parent node that would be more specific to this key
                // Let's get the base prefix of this child (id) and check if there are leaves
                let local_leaf_id = LeafId::new(id, STRIDE);
                let local_node_offset =
                    bitmap_index(parent_node.node_bitmap, id) - 1;
                if self.nodes[parent_node_index]
                    .leaf_bitmap
                    .find_leaf_lpm(local_leaf_id)
                    .is_some_and(|id| id == local_leaf_offset)
                {
                    let local_default = self.leaves
                        [(base_leaf_offset + local_leaf_offset) as usize]
                        .clone();
                    // Set default
                    self.nodes
                        [(base_node_offset + local_node_offset) as usize]
                        .default_value = Some(local_default);
                };
            }
        }
    }

    pub fn lookup(&self, key: u32) -> Option<T> {
        // TODO: Implement lookup algorithm
        let mut key_offset = 0;
        // First node is root
        let mut parent_node_index = 0;
        // TODO: Improve borrowing around parent_node (currently cloning)
        let mut parent_node = self.nodes[parent_node_index].clone();
        let mut default = None;
        if parent_node.default_value.is_some() {
            default = parent_node.default_value.clone();
        }

        let mut local_id = extract_bits(key, key_offset, STRIDE) as u8;

        // Should try internal nodes first, apparently
        while bitmap_contains(parent_node.node_bitmap, local_id as u8) {
            // Before anything, take a look at the default value

            // If there's a valid internal node, traverse it
            let base_node_offset = parent_node.node_offset;
            let local_offset =
                bitmap_index(parent_node.node_bitmap, local_id) - 1;

            parent_node_index = (base_node_offset + local_offset) as usize;
            parent_node = self.nodes[parent_node_index].clone(); // TODO: Optimize clone away

            if parent_node.default_value.is_some() {
                default = parent_node.default_value.clone();
            }

            // Update key offset and local ID
            key_offset += STRIDE;
            local_id = extract_bits(key, key_offset, STRIDE) as u8;
        }

        // (space and insert optimization) Check leaf at local_id and its parent prefixes
        // We start by calculating the prefix index - can be improved
        let remaining_length = min(STRIDE, 32 - key_offset);
        let local_prefix_id = LeafId::new(local_id, remaining_length);
        let base_leaf_offset = parent_node.leaf_offset;

        // Check leaves for receding prefixes
        if let Some(leaf_index) =
            parent_node.leaf_bitmap.find_leaf_lpm(local_prefix_id)
        {
            return Some(
                self.leaves[(base_leaf_offset + leaf_index) as usize].clone(),
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
            last_node.leaf_offset + last_node.leaf_bitmap.pop_count();
        let next_node_base =
            last_node.node_offset + last_node.node_bitmap.count_ones();

        (next_node_base, next_leaf_base)
    }
}

#[test]
fn test_find_leaf() {
    let mut trie = Poptrie::new();
    trie.insert(Prefix(u32::from_be_bytes([192, 168, 0, 0]), 30), 0);
    trie.insert(Prefix(u32::from_be_bytes([192, 168, 0, 1]), 32), 1);
    trie.insert(Prefix(u32::from_be_bytes([192, 168, 0, 2]), 32), 2);

    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 0])), Some(0));
    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 1])), Some(1));
    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 2])), Some(2));
    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 3])), Some(0));
}

#[test]
fn one_level_before() {
    let mut trie = Poptrie::new();
    trie.insert(Prefix(0b000001_000001_000001_000001_000000_00, 25), 0);
    trie.insert(Prefix(0b000001_000001_000001_000001_000001_01, 32), 1);
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
    let mut trie = Poptrie::new();
    trie.insert(Prefix(0b000001_000000_000000_000000_000000_00, 6), 0);
    trie.insert(Prefix(0b000000_000000_000000_000000_000000_00, 12), 1);
    assert_eq!(
        trie.lookup(0b000001_000000_000000_000000_000000_00),
        Some(0)
    );
    // Levels 2 and 3
    let mut trie = Poptrie::new();
    trie.insert(Prefix(0b000000_110000_000000_000000_000000_00, 12), 0);
    trie.insert(Prefix(0b000000_000000_000000_000000_000000_00, 18), 1);
    assert_eq!(
        trie.lookup(0b000000_110000_000000_000000_000000_00),
        Some(0)
    );
    // Levels 1 and 2 (non-full length)
    let mut trie = Poptrie::new();
    trie.insert(Prefix(0b001100_000000_000000_000000_000000_00, 10), 0);
    trie.insert(Prefix(0b000000_000000_000000_000000_000000_00, 1), 1);
    assert_eq!(
        trie.lookup(0b001100_000100_000000_000000_000000_00),
        Some(1)
    );
}

#[test]
fn default_overwrite() {
    let mut trie = Poptrie::new();
    trie.insert(Prefix(0b000000_000000_000000_000000_000000_00, 0), 0);
    trie.insert(Prefix(0b000001_000001_000000_000000_000000_00, 15), 2);
    trie.insert(Prefix(0b000000_000000_000000_000000_000000_00, 0), 1);
    assert_eq!(
        trie.lookup(0b000001_000001_001000_000000_000000_00),
        Some(1)
    );
}
