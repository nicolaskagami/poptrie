//! Core lookup-only types for poptrie.
//!
//! Contains [`PoptrieCore`] and [`Node`], the data that participates in
//! longest-prefix-match lookups. When the `rkyv` feature is enabled, these
//! types support zero-copy serialization.

use core::marker::PhantomData;

pub use crate::prefix::Prefix;

use alloc::vec::Vec;
use crate::bitmap::*;
use crate::value_index::ValueIndex;

/// The core of a compressed prefix tree optimized for fast longest prefix match (LPM) lookups.
///
/// This is the serializable subset of [`crate::Poptrie`]: it contains the node
/// tree, leaf mappings, and values, but excludes the `entries` map which stores
/// prefix metadata used only for mutation and iteration.
///
/// When the `rkyv` feature is enabled, [`PoptrieCore`] can be serialized with
/// `rkyv::to_bytes` and accessed zero-copy via [`ArchivedPoptrieCore::lookup`].
#[derive(Debug, Clone, Default)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize),
    rkyv(compare(PartialEq))
)]
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

    /// Pins the prefix type.
    pub(crate) _phantom: PhantomData<P>,
}

impl<P, V> PoptrieCore<P, V>
where
    P: Prefix,
{
    /// Lookup an address in the trie, performing longest-prefix match.
    ///
    /// Returns `None` if no prefix matches the key.
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
    /// assert_eq!(trie.into_core().len(), 1);
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
    /// assert!(!trie.into_core().is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

#[cfg(feature = "rkyv")]
impl<P, V> ArchivedPoptrieCore<P, V>
where
    P: Prefix,
    V: rkyv::Archive,
{
    /// Zero-copy longest-prefix-match lookup on an archived poptrie core.
    ///
    /// Returns `None` if no prefix matches the key.
    #[inline]
    pub fn lookup<A: Into<P::ADDRESS>>(
        &self,
        address: A,
    ) -> Option<&<V as rkyv::Archive>::Archived> {
        let address = address.into();

        let mut offset: u8 = 0;
        let mut parent_node_index = 0;
        let mut parent_node = &self.nodes[parent_node_index];

        let mut local_id = StrideId::from_address(address, offset, crate::STRIDE);

        // Traverse internal nodes via the archived bitmap accessors
        while parent_node.node_bitmap.contains(local_id) {
            parent_node_index = parent_node.get_child_index(local_id);
            parent_node = &self.nodes[parent_node_index];
            offset += crate::STRIDE;
            local_id = StrideId::from_address(address, offset, crate::STRIDE);
        }

        // Find the leaf for the remaining stride
        let leaf_index =
            parent_node.leaf_bitmap.leafvec_index( local_id);
        let leaf_base = u32::from(parent_node.leaf_base);

        // ArchivedValueIndex is Archived<u32> = rkyv::Endian<u32, LE>
        let archived_vi = &self.leaves[(leaf_base + leaf_index) as usize];
        let raw: u32 = archived_vi.0.into();

        if raw == u32::MAX {
            None
        } else {
            Some(&self.values[raw as usize])
        }
    }
}

/// An internal node in the trie
#[derive(Debug, Clone, Default)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize),
    rkyv(compare(PartialEq))
)]
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
        #[cfg(test)]
        debug_prefix: Vec<StrideId>,
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

#[cfg(feature = "rkyv",)]
impl ArchivedNode {
/// Returns the index of the child node pointed by `local_id`.
    #[inline(always)]
    pub(crate) fn get_child_index(&self, local_id: StrideId) -> usize {
        (self.node_base + self.node_bitmap.bitmap_index(local_id)) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_lookup_matches() {
        let mut core = PoptrieCore {
            nodes: Vec::new(),
            leaves: Vec::new(),
            values: Vec::<u32>::new(),
            _phantom: PhantomData::<(u32, u8)>,
        };

        let mut root = Node::new(
            #[cfg(test)]
            Vec::new(),
            1,
            0,
        );
        root.leaf_bitmap.set(StrideId(0));
        core.nodes.push(root);
        core.leaves.push(ValueIndex::NONE);

        assert_eq!(core.lookup(0u32), None);
    }

    #[cfg(feature = "rkyv")]
    #[test]
    fn core_roundtrip_u32() {
        let mut core = PoptrieCore {
            nodes: Vec::new(),
            leaves: Vec::new(),
            values: Vec::<u32>::new(),
            _phantom: PhantomData::<(u32, u8)>,
        };

        let mut root = Node::new(
            #[cfg(test)]
            Vec::new(),
            1,
            0,
        );
        root.leaf_bitmap.set(StrideId(0));
        core.nodes.push(root);
        core.leaves.push(ValueIndex::new(0));
        core.values.push(42u32);

        let bytes = rkyv::to_bytes::<rkyv::rancor::BoxedError>(&core).expect("serialization failed");
        let archived = rkyv::access::<ArchivedPoptrieCore<(u32, u8), u32>, rkyv::rancor::BoxedError>(&bytes)
            .expect("deserialization failed");
        
        assert_eq!(
            archived.lookup(0u32).map(|&v| u32::from(v)),
            Some(42)
        );
    }

    #[cfg(feature = "rkyv")]
    #[test]
    fn core_roundtrip_with_entries() {
        let mut trie = crate::Poptrie::<(u32, u8), u32>::new();
        trie.insert((0u32, 0), 0);
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8);
        trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16);
        trie.insert((u32::from_be_bytes([10, 1, 2, 0]), 24), 24);

        let core = trie.into_core();

        let bytes = rkyv::to_bytes::<rkyv::rancor::BoxedError>(&core).expect("serialization failed");
        let archived = rkyv::access::<ArchivedPoptrieCore<(u32, u8), u32>, rkyv::rancor::BoxedError>(&bytes)
            .expect("deserialization failed");

        assert_eq!(
            archived
                .lookup(u32::from_be_bytes([10, 1, 2, 3]))
                .map(|&v| u32::from(v)),
            Some(24)
        );
        assert_eq!(
            archived
                .lookup(u32::from_be_bytes([10, 0, 1, 1]))
                .map(|&v| u32::from(v)),
            Some(8)
        );
        assert_eq!(
            archived
                .lookup(u32::from_be_bytes([10, 1, 1, 1]))
                .map(|&v| u32::from(v)),
            Some(16)
        );
        assert_eq!(
            archived
                .lookup(u32::from_be_bytes([8, 8, 8, 8]))
                .map(|&v| u32::from(v)),
            Some(0)
        );
        assert_eq!(
            archived
                .lookup(u32::from_be_bytes([192, 168, 0, 1]))
                .map(|&v| u32::from(v)),
            Some(0)
        );
    }

    #[cfg(feature = "rkyv")]
    #[test]
    fn core_roundtrip_string_values() {
        let mut core = PoptrieCore {
            nodes: Vec::new(),
            leaves: Vec::new(),
            values: Vec::<alloc::string::String>::new(),
            _phantom: PhantomData::<(u32, u8)>,
        };

        let mut root = Node::new(
            #[cfg(test)]
            Vec::new(),
            1,
            0,
        );
        root.leaf_bitmap.set(StrideId(0));
        core.nodes.push(root);
        core.leaves.push(ValueIndex::new(0));
        core.values.push("default".into());

        let bytes = rkyv::to_bytes::<rkyv::rancor::BoxedError>(&core).expect("serialization failed");
        let archived =
            rkyv::access::<ArchivedPoptrieCore<(u32, u8), alloc::string::String>, rkyv::rancor::BoxedError>(&bytes)
                .expect("deserialization failed");

        assert_eq!(archived.lookup(0u32).map(|s| s.as_str()), Some("default"));
    }
}
