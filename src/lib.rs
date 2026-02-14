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
pub mod bitmap;

extern crate alloc;
use core::cmp::min;

use alloc::vec;
use alloc::vec::Vec;
use bitmap::*;

// Idea: u128 bitfield to 1-1 associate any leaf prefix
// (XXXXXX)(prefix length 0) -> 0
// (0XXXXX)(prefix length 1) -> 1
// (1XXXXX)(prefix length 1) -> 2
// ...
// We can get the the bit index like this:
// (prefix, len) -> 2^len + extract(prefix, len)
//
// When looking up an address, we'll have the full "prefix"
// Use the value above and divide by two until we get something (perhaps -1 before)
// Index can still be popcounted with 2 popcounts
//

#[derive(Debug, Clone)]
struct Node<T: Clone> {
    /// Bitmap of local nodes
    node_bitmap: u64,

    /// Bitmap of local prefixes
    leaf_bitmap: u128, // Optimization for storing exact prefixes with lengths
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
        node_offset: u32,
        leaf_offset: u32,
        default_value: Option<T>,
    ) -> Self {
        Node {
            node_bitmap: 0,
            leaf_bitmap: 0,
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
pub struct Prefix(u32, u8);

impl<T: Clone> Poptrie<T> {
    pub fn new() -> Self {
        Poptrie {
            // Starting with an empty root node
            nodes: vec![Node::new(1, 0, None)],
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

        // Keep track of parent's default
        let mut parent_default = parent_node.default_value.clone();

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

                // Setting the default value for the new node if there's a leaf that encompasses it
                if let Some(leaf_index) =
                    find_leaf_lpm(parent_node.leaf_bitmap, local_id)
                {
                    let leaf_default = self.leaves
                        [(base_leaf_offset + leaf_index) as usize]
                        .clone();
                    parent_default = Some(leaf_default);
                }
                self.nodes.insert(
                    (base_node_offset + local_node_offset) as usize,
                    Node::new(
                        base_node_offset,
                        base_leaf_offset,
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
            if parent_node.default_value.is_some() {
                parent_default = parent_node.default_value.clone();
            }
            key_offset += STRIDE;
        }

        let remaining_length = key_length - key_offset;
        let local_id = extract_bits(key, key_offset, remaining_length) as u8;
        // We don't need to clear the bits that are not used because the extraction function already does it for us.

        let leaf_id = bitmap_id_prefix_u128(local_id, remaining_length);

        // TODO: Keep only indices in leaves
        let base_leaf_offset = self.nodes[parent_node_index].leaf_offset;
        let mut local_leaf_offset =
            bitmap_index_u128(parent_node.leaf_bitmap, leaf_id);
        // Check if there is a leaf with the key
        if !bitmap_contains_u128(parent_node.leaf_bitmap, leaf_id) {
            // Create a new leaf node
            self.leaves
                .insert((base_leaf_offset + local_leaf_offset) as usize, value);

            // Update offsets after the index
            // Now we can insert leaves - It's relatively slow having to shift everything
            for i in parent_node_index + 1..self.nodes.len() {
                self.nodes[i].leaf_offset += 1;
            }

            // Set the leaf
            bitmap_set_u128(
                &mut self.nodes[parent_node_index].leaf_bitmap,
                leaf_id as u8,
            );
        } else {
            // Overwrite the existing leaf (-1 to correct index)
            local_leaf_offset -= 1;
            self.leaves[(base_leaf_offset + local_leaf_offset) as usize] =
                value;
        }
        // TODO: Insert default for internal nodes
        // Careful! Check the leaf bitmap of this node to see there are more specific prefixes... let's not think about delete just yet.
        // The default will be the /0 of that stride. If it explicitly exists in that subtree we shouldn't overwrite it.
        // Else, if it was set by one of our leaves... the longest prefix needs to win.

        // For every child node
        // let i = 0; // Could sub in for local_node_offset
        for id in 0..63 {
            // If it exists
            if bitmap_contains(parent_node.node_bitmap, id) {
                // Check if there is a leaf node in this parent node that would be more specific to this key
                // Let's get the base prefix of this child (id) and check if there are leaves
                let local_id = id;
                let local_node_offset =
                    bitmap_index(parent_node.node_bitmap, local_id) - 1;
                if find_leaf_lpm(
                    self.nodes[parent_node_index].leaf_bitmap,
                    local_id,
                )
                .is_some_and(|id| id == (base_leaf_offset + local_leaf_offset))
                {
                    let local_default = self.leaves
                        [(base_leaf_offset + local_leaf_offset) as usize]
                        .clone();
                    // Set default
                    self.nodes
                        [(base_leaf_offset + local_node_offset) as usize]
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
        local_id = bitmap_id_prefix_u128(local_id, remaining_length);
        let base_leaf_offset = parent_node.leaf_offset;

        // Check leaves for receding prefixes
        if let Some(leaf_index) =
            find_leaf_lpm(parent_node.leaf_bitmap, local_id)
        {
            return Some(
                self.leaves[(base_leaf_offset + leaf_index) as usize].clone(),
            );
        }
        // TODO: Check on index (should it use base?)
        default
    }
}

/// Returns leaf index for the prefix
fn find_leaf_lpm(leaf_bitmap: u128, mut local_id: u8) -> Option<u32> {
    loop {
        if bitmap_contains_u128(leaf_bitmap, local_id) {
            break Some(bitmap_index_u128(leaf_bitmap, local_id) - 1);
        }
        if local_id == 0 {
            break None;
        };
        // Subtract 1 and divide by 2
        local_id = (local_id - 1) >> 1;
    }
}

#[test]
fn test_find_leaf() {
    let mut trie = Poptrie::new();
    trie.insert(Prefix(u32::from_be_bytes([192, 168, 0, 0]), 30), 0);
    // trie.insert(Prefix(u32::from_be_bytes([192, 168, 0, 1]), 32), 1);
    // trie.insert(Prefix(u32::from_be_bytes([192, 168, 0, 2]), 32), 2);

    // assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 0])), Some(0));
    // assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 1])), Some(1));
    // assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 2])), Some(2));
    // assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 0, 3])), Some(0));
}

#[test]
fn easy() {
    let mut trie = Poptrie::new();
    trie.insert(Prefix(0b000001_000001_000001_000001_000001_00, 31), 0);
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
fn one_level_before() {
    let mut trie = Poptrie::new();
    trie.insert(Prefix(0b000001_000001_000001_000001_000001_00, 25), 0);
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
