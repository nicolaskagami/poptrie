use crate::{
    Entry, Key, Node, Poptrie, STRIDE,
    bitmap::{PrefixId, StrideId},
    value_index::ValueIndex,
};
use alloc::{collections::btree_map, vec};
use alloc::{collections::btree_map::BTreeMap, vec::Vec};

impl<K: Key, V> FromIterator<((K, u8), V)> for Poptrie<K, V> {
    /// Creates a [`Poptrie`] from an iterator of `((key, prefix_length), value)` tuples.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let trie: Poptrie<u32, u32> = [
    ///     ((u32::from_be_bytes([10, 0, 0, 0]), 8), 8),
    ///     ((u32::from_be_bytes([10, 1, 0, 0]), 16), 16),
    /// ].into_iter().collect();
    ///
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&16));
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 2, 1, 1])), Some(&8));
    /// ```
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
                    .insert(prefix_id, ((key, len), current_value_index));
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

/// An owning iterator over the entries of a [`Poptrie`], in lexicographic
/// order of `(prefix_length, key)`.
///
/// This `struct` is created by the [`into_iter`] method on [`Poptrie`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
pub struct IntoIter<K: Key, V> {
    entries: vec::IntoIter<BTreeMap<PrefixId, Entry<K>>>,
    current: btree_map::IntoIter<PrefixId, Entry<K>>,
    values: alloc::vec::Vec<Option<V>>,
}

impl<K: Key, V> Iterator for IntoIter<K, V> {
    type Item = ((K, u8), V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            for (_, ((key, key_len), value_index)) in &mut self.current {
                if let Some(value) =
                    value_index.get().and_then(|idx| self.values[idx].take())
                {
                    return Some(((key, key_len), value));
                }
            }
            self.current = self.entries.next()?.into_iter();
        }
    }
}

impl<K: Key, V> IntoIterator for Poptrie<K, V> {
    type Item = ((K, u8), V);
    type IntoIter = IntoIter<K, V>;

    /// Consumes the trie and iterates over all `((key, prefix_length), value)`
    /// tuples, in lexicographic order of `(prefix_length, key)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, "10/8");
    /// trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, "10.1/16");
    ///
    /// let entries: Vec<_> = trie.into_iter().collect();
    /// assert_eq!(entries, [
    ///     ((u32::from_be_bytes([10, 0, 0, 0]), 8), "10/8"),
    ///     ((u32::from_be_bytes([10, 1, 0, 0]), 16), "10.1/16"),
    /// ]);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        let values = self.values.into_iter().map(Some).collect();
        let mut entries = self.entries.into_iter();
        let current = entries.next().unwrap_or_default().into_iter();

        IntoIter { entries, current, values }
    }
}

/// A borrowing iterator over the entries of a [`Poptrie`], in lexicographic
/// order of `(prefix_length, key)`.
///
/// This `struct` is created by the [`iter`] method on [`Poptrie`].
/// See its documentation for more.
///
/// [`iter`]: Poptrie::iter
pub struct Iter<'a, K: Key, V> {
    entries: core::slice::Iter<'a, BTreeMap<PrefixId, Entry<K>>>,
    current: btree_map::Iter<'a, PrefixId, Entry<K>>,
    values: &'a [V],
}

impl<'a, K: Key, V> Iterator for Iter<'a, K, V> {
    type Item = ((&'a K, u8), &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            for (_, ((key, key_len), value_index)) in &mut self.current {
                if let Some(idx) = value_index.get() {
                    return Some(((key, *key_len), &self.values[idx]));
                }
            }
            self.current = self.entries.next()?.iter();
        }
    }
}

impl<K: Key, V> Poptrie<K, V> {
    /// Iterates over all `((&key, prefix_length), &value)` tuples, in
    /// lexicographic order of `(prefix_length, key)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, "10/8");
    /// trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, "10.1/16");
    ///
    /// for ((key, len), val) in trie.iter() {
    ///     assert!(trie.contains_key(*key, len));
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        let mut entries = self.entries.iter();
        let current = entries.next().map(|m| m.iter()).unwrap_or_default();

        Iter { entries, current, values: &self.values }
    }
}

/// A mutable borrowing iterator over the entries of a [`Poptrie`], in
/// lexicographic order of `(prefix_length, key)`.
///
/// This `struct` is created by the [`iter_mut`] method on [`Poptrie`].
/// See its documentation for more.
///
/// [`iter_mut`]: Poptrie::iter_mut
pub struct IterMut<'a, K: Key, V> {
    entries: core::slice::Iter<'a, BTreeMap<PrefixId, Entry<K>>>,
    current: btree_map::Iter<'a, PrefixId, Entry<K>>,
    values: &'a mut [V],
}

impl<'a, K: Key, V> Iterator for IterMut<'a, K, V> {
    type Item = ((&'a K, u8), &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            for (_, ((key, key_len), value_index)) in &mut self.current {
                if let Some(idx) = value_index.get() {
                    // SAFETY: Each ValueIndex is unique across all entries so
                    // no two yielded references alias.
                    return Some(((key, *key_len), unsafe {
                        &mut *self.values.as_mut_ptr().add(idx)
                    }));
                }
            }
            self.current = self.entries.next()?.iter();
        }
    }
}

impl<K: Key, V> Poptrie<K, V> {
    /// Iterates mutably over all `((&key, prefix_length), &mut value)` tuples,
    /// in lexicographic order of `(prefix_length, key)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 1u32);
    /// trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 2u32);
    ///
    /// for ((key, len), val) in trie.iter_mut() {
    ///     *val *= 10;
    /// }
    ///
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 0, 1, 1])), Some(&10));
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&20));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        let Poptrie { entries, values, .. } = self;
        let mut entries_iter = entries.iter();
        let current = entries_iter.next().map(|m| m.iter()).unwrap_or_default();
        IterMut {
            entries: entries_iter,
            current,
            values: values.as_mut_slice(),
        }
    }
}

/// An iterator over the keys of a [`Poptrie`], in lexicographic order of
/// `(prefix_length, key)`.
///
/// This `struct` is created by the [`keys`] method on [`Poptrie`].
/// See its documentation for more.
///
/// [`keys`]: Poptrie::keys
pub struct Keys<'a, K: Key, V>(pub(crate) Iter<'a, K, V>);

impl<'a, K: Key, V> Iterator for Keys<'a, K, V> {
    type Item = (&'a K, u8);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|((k, l), _)| (k, l))
    }
}

/// An iterator over the values of a [`Poptrie`], in lexicographic order of
/// `(prefix_length, key)`.
///
/// This `struct` is created by the [`values`] method on [`Poptrie`].
/// See its documentation for more.
///
/// [`values`]: Poptrie::values
pub struct Values<'a, K: Key, V>(pub(crate) Iter<'a, K, V>);

impl<'a, K: Key, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }
}

/// A mutable iterator over the values of a [`Poptrie`], in lexicographic
/// order of `(prefix_length, key)`.
///
/// This `struct` is created by the [`values_mut`] method on [`Poptrie`].
/// See its documentation for more.
///
/// [`values_mut`]: Poptrie::values_mut
pub struct ValuesMut<'a, K: Key, V>(pub(crate) IterMut<'a, K, V>);

impl<'a, K: Key, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iter_yields_all_entries() {
        let mut trie = Poptrie::new();
        trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 8u32);
        trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 16u32);

        let entries: Vec<_> =
            trie.iter().map(|((k, l), v)| (*k, l, *v)).collect();
        assert_eq!(
            entries,
            [
                (u32::from_be_bytes([10, 0, 0, 0]), 8, 8),
                (u32::from_be_bytes([10, 1, 0, 0]), 16, 16),
            ]
        );
    }

    #[test]
    fn iter_empty_trie() {
        assert_eq!(Poptrie::<u32, u32>::new().iter().count(), 0);
    }

    #[test]
    fn into_iter_consumes_all_entries() {
        let mut trie = Poptrie::new();
        trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 8u32);
        trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 16u32);

        let entries: Vec<_> = trie.into_iter().collect();
        assert_eq!(
            entries,
            [
                ((u32::from_be_bytes([10, 0, 0, 0]), 8), 8),
                ((u32::from_be_bytes([10, 1, 0, 0]), 16), 16),
            ]
        );
    }

    #[test]
    fn into_iter_empty_trie() {
        assert_eq!(Poptrie::<u32, u32>::new().into_iter().count(), 0);
    }

    #[test]
    fn iter_mut_modifies_values() {
        let mut trie = Poptrie::new();
        trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 1u32);
        trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 2u32);

        for (_, v) in trie.iter_mut() {
            *v *= 10;
        }

        assert_eq!(trie.lookup(u32::from_be_bytes([10, 0, 1, 1])), Some(&10));
        assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&20));
    }

    #[test]
    fn iter_after_remove() {
        let mut trie = Poptrie::new();
        trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 8u32);
        trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 16u32);
        trie.remove(u32::from_be_bytes([10, 1, 0, 0]), 16);

        let entries: Vec<_> = trie.iter().collect();
        assert_eq!(entries.len(), 1);
        assert_eq!(*entries[0].0.0, u32::from_be_bytes([10, 0, 0, 0]));
        assert_eq!(entries[0].0.1, 8);
    }

    #[test]
    fn from_iter_round_trips_with_into_iter() {
        let mut trie = Poptrie::new();
        trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 8u32);
        trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 16u32);
        trie.insert(u32::from_be_bytes([10, 1, 2, 0]), 24, 24u32);

        let rebuilt: Poptrie<u32, u32> = trie.into_iter().collect();

        let entries: Vec<_> = rebuilt.into_iter().collect();
        assert_eq!(
            entries,
            [
                ((u32::from_be_bytes([10, 0, 0, 0]), 8), 8),
                ((u32::from_be_bytes([10, 1, 0, 0]), 16), 16),
                ((u32::from_be_bytes([10, 1, 2, 0]), 24), 24),
            ]
        );
    }

    #[test]
    fn iter_contains_key_consistent() {
        let mut trie = Poptrie::new();
        trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 8u32);
        trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 16u32);

        for ((key, len), _) in trie.iter() {
            assert!(trie.contains_key(*key, len));
        }
    }

    #[test]
    fn iter_is_sorted() {
        let mut trie = Poptrie::new();
        trie.insert(u32::from_be_bytes([10, 1, 0, 0]), 16, 16u32);
        trie.insert(u32::from_be_bytes([192, 168, 0, 0]), 16, 160u32);
        trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, 8u32);
        trie.insert(u32::from_be_bytes([10, 1, 2, 0]), 24, 24u32);

        let entries: Vec<_> = trie.iter().map(|((k, l), _)| (*k, l)).collect();
        assert_eq!(
            entries,
            [
                (u32::from_be_bytes([10, 0, 0, 0]), 8),
                (u32::from_be_bytes([10, 1, 0, 0]), 16),
                (u32::from_be_bytes([192, 168, 0, 0]), 16),
                (u32::from_be_bytes([10, 1, 2, 0]), 24),
            ]
        );
    }
}
