use core::mem;

use crate::{
    Entry, Poptrie, Prefix, bitmap::PrefixId, inner::PoptrieCore
};
use alloc::{collections::btree_map, vec};
use alloc::{collections::btree_map::BTreeMap, vec::Vec};

impl<P: Prefix, V> FromIterator<(P, V)> for Poptrie<P, V> {
    /// Creates a [`Poptrie`] from an iterator of `(prefix, value)` tuples.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let trie: Poptrie<(u32, u8), u32> = [
    ///     ((u32::from_be_bytes([10, 0, 0, 0]), 8), 8),
    ///     ((u32::from_be_bytes([10, 1, 0, 0]), 16), 16),
    /// ].into_iter().collect();
    ///
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&16));
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 2, 1, 1])), Some(&8));
    /// ```
    fn from_iter<I: IntoIterator<Item = (P, V)>>(iter: I) -> Self {
        Self::from_entries(iter)
    }
}

impl<P: Prefix, V> Extend<(P, V)> for Poptrie<P, V> {
    /// Bulk-inserts entries into the trie, merging them with existing entries.
    ///
    /// For large batches this is more efficient than calling
    /// [`insert`](Self::insert) in a loop: it rebuilds the trie breadth-first,
    /// computing node bases and leaves once instead of shifting the internal
    /// vectors on every insertion.
    ///
    /// Inserting a new prefix with the same value as an existing prefix replaces it
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.bulk_insert([
    ///     ((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32),
    ///     ((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32),
    /// ]);
    ///
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&16));
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 2, 1, 1])), Some(&8));
    /// ```
    fn extend<I: IntoIterator<Item = (P, V)>>(&mut self, iter: I) {
        if self.is_empty() {
            *self = Self::from_entries(iter);
            return;
        }

        // Merge-and-rebuild: existing entries first, new entries after, so new
        // entries win on duplicates. `into_iter` moves values out without
        // requiring `V: Clone`.
        let old = mem::replace(self, Self::new());
        *self = Self::from_entries(old.into_iter().chain(iter));
    }
}

/// An owning iterator over the entries of a [`Poptrie`], in lexicographic
/// order of `(prefix_length, key)`.
///
/// This `struct` is created by the [`into_iter`] method on [`Poptrie`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
pub struct IntoIter<P: Prefix, V> {
    entries: vec::IntoIter<BTreeMap<PrefixId, Entry<P>>>,
    current: btree_map::IntoIter<PrefixId, Entry<P>>,
    values: alloc::vec::Vec<Option<V>>,
}

impl<P: Prefix, V> Iterator for IntoIter<P, V> {
    type Item = (P, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            for (_, (prefix, value_index)) in &mut self.current {
                if let Some(value) =
                    value_index.get().and_then(|idx| self.values[idx].take())
                {
                    return Some((prefix, value));
                }
            }
            self.current = self.entries.next()?.into_iter();
        }
    }
}

impl<P: Prefix, V> IntoIterator for Poptrie<P, V> {
    type Item = (P, V);
    type IntoIter = IntoIter<P, V>;

    /// Consumes the trie and iterates over all `(prefix, value)` tuples, in
    /// lexicographic order of `(prefix_length, key)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), "10/8");
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), "10.1/16");
    ///
    /// let entries: Vec<_> = trie.into_iter().collect();
    /// assert_eq!(entries, [
    ///     ((u32::from_be_bytes([10, 0, 0, 0]), 8), "10/8"),
    ///     ((u32::from_be_bytes([10, 1, 0, 0]), 16), "10.1/16"),
    /// ]);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        let values = self.inner.values.into_iter().map(Some).collect();
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
pub struct Iter<'a, P: Prefix, V> {
    entries: core::slice::Iter<'a, BTreeMap<PrefixId, Entry<P>>>,
    current: btree_map::Iter<'a, PrefixId, Entry<P>>,
    values: &'a [V],
}

impl<'a, P: Prefix, V> Iterator for Iter<'a, P, V> {
    type Item = (&'a P, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            for (_, (prefix, value_index)) in &mut self.current {
                if let Some(idx) = value_index.get() {
                    return Some((prefix, &self.values[idx]));
                }
            }
            self.current = self.entries.next()?.iter();
        }
    }
}

impl<P: Prefix, V> Poptrie<P, V> {
    /// Iterates over all `(&prefix, &value)` pairs, in lexicographic order of
    /// `(prefix_length, key)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), "10/8");
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), "10.1/16");
    ///
    /// for (prefix, val) in trie.iter() {
    ///     assert!(trie.contains_key(*prefix));
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, P, V> {
        let mut entries = self.entries.iter();
        let current = entries.next().map(|m| m.iter()).unwrap_or_default();
        Iter { entries, current, values: &self.inner.values }
    }
}

/// A mutable borrowing iterator over the entries of a [`Poptrie`], in
/// lexicographic order of `(prefix_length, key)`.
///
/// This `struct` is created by the [`iter_mut`] method on [`Poptrie`].
/// See its documentation for more.
///
/// [`iter_mut`]: Poptrie::iter_mut
pub struct IterMut<'a, P: Prefix, V> {
    entries: core::slice::Iter<'a, BTreeMap<PrefixId, Entry<P>>>,
    current: btree_map::Iter<'a, PrefixId, Entry<P>>,
    values: Vec<Option<&'a mut V>>, // Could be 15% faster with unsafe
}

impl<'a, P: Prefix, V> Iterator for IterMut<'a, P, V> {
    type Item = (&'a P, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            for (_, (prefix, value_index)) in &mut self.current {
                if let Some(idx) = value_index.get() {
                    // SAFETY: Each ValueIndex is unique across all entries so
                    // no two yielded references alias.
                    return Some((prefix, self.values[idx].take().unwrap()));
                }
            }
            self.current = self.entries.next()?.iter();
        }
    }
}

impl<P: Prefix, V> Poptrie<P, V> {
    /// Iterates mutably over all `(&prefix, &mut value)` pairs, in lexicographic
    /// order of `(prefix_length, key)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use poptrie::Poptrie;
    ///
    /// let mut trie = Poptrie::new();
    /// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 1u32);
    /// trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 2u32);
    ///
    /// for (_, val) in trie.iter_mut() {
    ///     *val *= 10;
    /// }
    ///
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 0, 1, 1])), Some(&10));
    /// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&20));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, P, V> {
        let Poptrie { entries, inner: PoptrieCore { values, .. },  .. } = self;
        let mut entries_iter = entries.iter();
        let current = entries_iter.next().map(|m| m.iter()).unwrap_or_default();
        IterMut {
            entries: entries_iter,
            current,
            values: values.iter_mut().map(Some).collect(),
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
pub struct Keys<'a, P: Prefix, V>(pub(crate) Iter<'a, P, V>);

impl<'a, P: Prefix, V> Iterator for Keys<'a, P, V> {
    type Item = &'a P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

/// An iterator over the values of a [`Poptrie`], in lexicographic order of
/// `(prefix_length, key)`.
///
/// This `struct` is created by the [`values`] method on [`Poptrie`].
/// See its documentation for more.
///
/// [`values`]: Poptrie::values
pub struct Values<'a, P: Prefix, V>(pub(crate) Iter<'a, P, V>);

impl<'a, P: Prefix, V> Iterator for Values<'a, P, V> {
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
pub struct ValuesMut<'a, P: Prefix, V>(pub(crate) IterMut<'a, P, V>);

impl<'a, P: Prefix, V> Iterator for ValuesMut<'a, P, V> {
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
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
        trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);

        let entries: Vec<_> = trie.iter().map(|(p, v)| (*p, *v)).collect();
        assert_eq!(
            entries,
            [
                ((u32::from_be_bytes([10, 0, 0, 0]), 8), 8),
                ((u32::from_be_bytes([10, 1, 0, 0]), 16), 16),
            ]
        );
    }

    #[test]
    fn iter_empty_trie() {
        assert_eq!(Poptrie::<(u32, u8), u32>::new().iter().count(), 0);
    }

    #[test]
    fn into_iter_consumes_all_entries() {
        let mut trie = Poptrie::new();
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
        trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);

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
        assert_eq!(Poptrie::<(u32, u8), u32>::new().into_iter().count(), 0);
    }

    #[test]
    fn iter_mut_modifies_values() {
        let mut trie = Poptrie::new();
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 1u32);
        trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 2u32);

        for (_, v) in trie.iter_mut() {
            *v *= 10;
        }

        assert_eq!(trie.lookup(u32::from_be_bytes([10, 0, 1, 1])), Some(&10));
        assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&20));
    }

    #[test]
    fn iter_after_remove() {
        let mut trie = Poptrie::new();
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
        trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);
        trie.remove((u32::from_be_bytes([10, 1, 0, 0]), 16));

        let entries: Vec<_> = trie.iter().collect();
        assert_eq!(entries.len(), 1);
        assert_eq!(*entries[0].0, (u32::from_be_bytes([10, 0, 0, 0]), 8));
    }

    #[test]
    fn from_iter_round_trips_with_into_iter() {
        let mut trie = Poptrie::new();
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
        trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);
        trie.insert((u32::from_be_bytes([10, 1, 2, 0]), 24), 24u32);

        let rebuilt: Poptrie<(u32, u8), u32> = trie.into_iter().collect();

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
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
        trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);

        for (prefix, _) in trie.iter() {
            assert!(trie.contains_key(*prefix));
        }
    }

    #[test]
    fn iter_is_sorted() {
        let mut trie = Poptrie::new();
        trie.insert((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32);
        trie.insert((u32::from_be_bytes([192, 168, 0, 0]), 16), 160u32);
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);
        trie.insert((u32::from_be_bytes([10, 1, 2, 0]), 24), 24u32);

        let entries: Vec<_> = trie.iter().map(|(p, _)| *p).collect();
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
