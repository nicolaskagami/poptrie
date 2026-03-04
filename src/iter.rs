use crate::{
    Key, Node, Poptrie, STRIDE,
    bitmap::{PrefixId, StrideId, find_leaf_lpm},
    value_index::ValueIndex,
};
use alloc::vec;
use alloc::{collections::btree_map::BTreeMap, vec::Vec};

impl<K: Key, V> FromIterator<((K, u8), V)> for Poptrie<K, V> {
    fn from_iter<I: IntoIterator<Item = ((K, u8), V)>>(iter: I) -> Self {
        let mut poptrie = Self::new();

        let mut items: Vec<_> = iter
            .into_iter()
            .map(|((key, len), value)| {
                let path: Vec<_> = (0..(len / STRIDE))
                    .map(|i| StrideId::from_key(key, i * STRIDE, STRIDE))
                    .collect();
                // Let's keep the path and the last parent
                (path, len, key, value, 0)
            })
            .collect();

        // Let's sort by lexicographical path
        items.sort_by(|(a_path, ..), (b_path, ..)| a_path.cmp(b_path));

        // We go breadth-first, level by level:
        // - Insert the would-be leaves into reference.
        // - Insert the new internal nodes for that level, along with their defaults.
        // - Fix the parent's bitmaps with the information above.
        let mut defaults = vec![ValueIndex::NONE];
        let mut level = 0;

        // Keeping track of node count and which nodes need to have their node bases set.
        let mut node_count = 1;
        let mut nodes_to_process = 0..1;

        while !items.is_empty() {
            // Remove all leaves for this level and add them to reference
            for (path, len, key, value, mut parent_node_index) in
                items.extract_if(.., |(path, _, _, _, _)| path.len() <= level)
            {
                poptrie.values.push(value);
                let current_value_index =
                    ValueIndex::new((poptrie.values.len() - 1) as u32);

                if level > 0 {
                    let local_id = path[level - 1];
                    let full_node_index = (poptrie.nodes[parent_node_index]
                        .node_base
                        + poptrie.nodes[parent_node_index]
                            .node_bitmap
                            .bitmap_index(local_id))
                        as usize;
                    parent_node_index = full_node_index;
                }

                let key_offset = path.len() as u8 * STRIDE;
                let remaining_length = len - key_offset;
                let prefix_id =
                    PrefixId::from_key(key, key_offset, remaining_length);
                poptrie.reference[parent_node_index]
                    .insert(prefix_id, current_value_index);
            }

            // Deal with all internal nodes of this level
            for (path, _, _, _, parent_node_index) in items.iter_mut() {
                // Point of this is calculating the bitmap count and node_base of the nodes in level -1
                // We MUST have already added its parents
                if level > 0 {
                    let local_id = path[level - 1];
                    let full_node_index = (poptrie.nodes[*parent_node_index]
                        .node_base
                        + poptrie.nodes[*parent_node_index]
                            .node_bitmap
                            .bitmap_index(local_id))
                        as usize;
                    *parent_node_index = full_node_index;
                }
                let local_id = path[level];
                // Add node if it doesn't exist
                if !poptrie.nodes[*parent_node_index]
                    .node_bitmap
                    .contains(local_id)
                {
                    poptrie.nodes.push(Node::default());
                    poptrie.nodes[*parent_node_index].node_bitmap.set(local_id);
                    poptrie.reference.push(BTreeMap::new());

                    // The parent must be ready to provide a default
                    let prefix_id = PrefixId::new(local_id.0, STRIDE).parent();
                    let default = find_leaf_lpm(
                        &poptrie.reference[*parent_node_index],
                        prefix_id,
                    )
                    .unwrap_or(defaults[*parent_node_index]);
                    defaults.push(default);
                }
            }

            // Now we can calculate node bases for all nodes of level-1 since they have the correct bitmaps.
            // TODO: don't recalculate so much - we should only do it on for level-1
            for node in poptrie.nodes[nodes_to_process.clone()].iter_mut() {
                node.node_base = node_count;
                node_count += node.node_bitmap.pop_count();
            }
            nodes_to_process = nodes_to_process.end..poptrie.nodes.len();

            level += 1;
        }

        // Now we need to calculate leaf bases and expand the leaves for all the parents of leaves (nodes in level)
        let _ = poptrie.calculate_leaf_ranges(0, ValueIndex::NONE);
        // Allow: `i` is used in `calculate_leaf_ranges` and that borrows mutably so we can't iter_mut
        #[allow(clippy::needless_range_loop)]
        for i in 1..poptrie.nodes.len() {
            poptrie.nodes[i].leaf_base = poptrie.leaves.len() as u32;

            poptrie.build_leaf_ranges(i, defaults[i]);
        }

        poptrie
    }
}
