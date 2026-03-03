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
                (path, len, key, value)
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
        while !items.is_empty() {
            // Remove all leaves for this level and add them to reference
            for (path, len, key, value) in
                items.extract_if(.., |(path, _, _, _)| path.len() <= level)
            {
                poptrie.values.push(value);
                let current_value_index =
                    ValueIndex::new((poptrie.values.len() - 1) as u32);

                let mut parent_node_index = 0;
                for &local_id in &path {
                    let full_node_index = (poptrie.nodes[parent_node_index]
                        .node_base
                        + poptrie.nodes[parent_node_index]
                            .node_bitmap
                            .bitmap_index(local_id))
                        as usize;
                    // We MUST have already added its parents
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
            for (path, _, _, _) in &items {
                // Point of this is calculating the bitmap count and node_base of the nodes in level -1
                let mut parent_node_index = 0;
                for local_id in path.iter().take(level) {
                    let full_node_index = (poptrie.nodes[parent_node_index]
                        .node_base
                        + poptrie.nodes[parent_node_index]
                            .node_bitmap
                            .bitmap_index(*local_id))
                        as usize;
                    // We MUST have already added its parents
                    parent_node_index = full_node_index;
                }

                // Add node if it doesn't exist
                let local_id = path[level];
                if !poptrie.nodes[parent_node_index]
                    .node_bitmap
                    .contains(local_id)
                {
                    poptrie.nodes.push(Node::new(
                        #[cfg(test)]
                        [
                            poptrie.nodes[parent_node_index]
                                .debug_prefix
                                .as_slice(),
                            &[local_id],
                        ]
                        .concat(),
                        0, // To be fixed later
                        0, // To be fixed later
                    ));

                    poptrie.nodes[parent_node_index].node_bitmap.set(local_id);
                    poptrie.reference.push(BTreeMap::new());

                    // The parent must be ready to provide a default
                    let prefix_id = PrefixId::new(local_id.0, STRIDE).parent();
                    let default = find_leaf_lpm(
                        &poptrie.reference[parent_node_index],
                        prefix_id,
                    )
                    .unwrap_or(defaults[parent_node_index]);
                    defaults.push(default);
                }
            }

            // Now we can calculate node bases for all nodes of level-1 since they have the correct bitmaps.
            // TODO: don't recalculate so much - we should only do it on for level-1
            let mut node_count = 1;
            for node in poptrie.nodes.iter_mut() {
                node.node_base = node_count;
                node_count += node.node_bitmap.pop_count();
            }

            level += 1;
        }

        // Now we need to calculate leaf bases and expand the leaves for all the parents of leaves (nodes in level)
        // Allow: `i` is used in `calculate_leaf_ranges` and that borrows mutably so we can't iter_mut
        #[allow(clippy::needless_range_loop)]
        for i in 0..poptrie.nodes.len() {
            poptrie.nodes[i].leaf_base = poptrie.leaves.len() as u32;
            poptrie.leaves.push(ValueIndex::NONE);
            poptrie.nodes[i].leaf_bitmap.set(StrideId(0));

            let _ = poptrie.calculate_leaf_ranges(i, defaults[i]);
        }

        poptrie
    }
}
