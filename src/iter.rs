use crate::{
    Key, Node, Poptrie, STRIDE,
    bitmap::{PrefixId, StrideId},
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
                // Let's add the path and the last parent
                (path, 0, len, key, value)
            })
            .collect();

        // Let's sort by lexicographical path
        items.sort_by(|(a_path, ..), (b_path, ..)| a_path.cmp(b_path));

        // We go breadth-first, level by level:
        // - Insert the would-be leaves into entries.
        // - Insert the new internal nodes for that level, along with their defaults.
        // - Fix the parent's bitmaps with the information above.
        let mut defaults = vec![ValueIndex::NONE];
        let mut level = 0;

        // Keeping track of node count and which nodes need to have their node bases set.
        let mut node_count = 1;
        let mut nodes_to_process = 0..1;

        while !items.is_empty() {
            // Remove all leaves for this level and add them to entries
            for (path, mut parent_node_index, len, key, value) in
                items.extract_if(.., |(path, ..)| path.len() <= level)
            {
                poptrie.values.push(value);
                let current_value_index =
                    ValueIndex::new((poptrie.values.len() - 1) as u32);

                if level > 0 {
                    let local_id = path[level - 1];
                    parent_node_index = poptrie.nodes[parent_node_index]
                        .get_child_index(local_id);
                }

                let key_offset = path.len() as u8 * STRIDE;
                let remaining_length = len - key_offset;
                let prefix_id =
                    PrefixId::from_key(key, key_offset, remaining_length);
                poptrie.entries[parent_node_index]
                    .insert(prefix_id, current_value_index);
            }

            // Last step allows us to calculate the leaves
            for i in nodes_to_process.clone() {
                poptrie.nodes[i].leaf_base = poptrie.leaves.len() as u32;
                poptrie.build_leaf_ranges_bulk_insert(i, defaults[i]);
            }

            // Deal with all internal nodes of this level
            // Having the leaves calculated for level-1 allows us to use the leafvec in this
            // following step instead of the `find_leaf_lpm`.
            for (path, parent_node_index, ..) in items.iter_mut() {
                // Point of this is calculating the bitmap count and node_base of the nodes in level -1
                // We MUST have already added its parents
                if level > 0 {
                    let local_id = path[level - 1];
                    *parent_node_index = poptrie.nodes[*parent_node_index]
                        .get_child_index(local_id);
                }
                let local_id = path[level];
                // Add node if it doesn't exist
                if !poptrie.nodes[*parent_node_index]
                    .node_bitmap
                    .contains(local_id)
                {
                    poptrie.nodes.push(Node::default());
                    poptrie.nodes[*parent_node_index].node_bitmap.set(local_id);
                    poptrie.entries.push(BTreeMap::new());

                    // The parent must be ready to provide a default
                    defaults.push(
                        poptrie.get_default(*parent_node_index, local_id),
                    );
                }
            }

            // Now we can calculate node bases for all nodes of level-1 since they have the correct bitmaps.
            for node in poptrie.nodes[nodes_to_process.clone()].iter_mut() {
                node.node_base = node_count;
                node_count += node.node_bitmap.pop_count();
            }
            nodes_to_process = nodes_to_process.end..poptrie.nodes.len();

            level += 1;
        }

        poptrie
    }
}
