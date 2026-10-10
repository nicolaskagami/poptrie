use poptrie::Poptrie;

#[test]
fn bulk_insert_duplicates_keep_last_value() {
    let entries = [
        ((u32::from_be_bytes([10, 0, 0, 0]), 8), 1u32),
        ((u32::from_be_bytes([10, 0, 0, 0]), 8), 2u32),
    ];

    let trie: Poptrie<_, _> = entries.into_iter().collect();

    assert_eq!(trie.len(), 1);
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&2));
}

#[test]
fn bulk_insert_empty_is_noop() {
    let mut trie = Poptrie::new();
    trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);

    let none: Vec<((u32, u8), u32)> = Vec::new();
    trie.extend(none);

    assert_eq!(trie.len(), 1);
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&8));
}

#[test]
fn bulk_insert_merges_with_existing_trie() {
    let mut trie = Poptrie::new();
    trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);

    trie.extend([
        ((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32),
        ((u32::from_be_bytes([192, 168, 0, 0]), 16), 24u32),
    ]);

    assert_eq!(trie.len(), 3);
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&16));
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 2, 1, 1])), Some(&8));
    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 1, 1])), Some(&24));
}

#[test]
fn bulk_insert_replaces_existing_prefix_small_batch() {
    let mut trie = Poptrie::new();
    trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);

    trie.extend([((u32::from_be_bytes([10, 0, 0, 0]), 8), 99u32)]);

    assert_eq!(trie.len(), 1);
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&99));
}

#[test]
fn bulk_insert_large_batch_uses_rebuild() {
    let mut trie = Poptrie::new();
    trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);

    // 34 entries exceed the small-batch fallback, forcing the rebuild path.
    let mut batch: Vec<_> = (0..33u8)
        .map(|i| ((u32::from_be_bytes([192, 168, i, 0]), 24), i as u32))
        .collect();
    // Replaces the existing /8 through the rebuild path.
    batch.push(((u32::from_be_bytes([10, 0, 0, 0]), 8), 100u32));

    trie.extend(batch);

    assert_eq!(trie.len(), 34);
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&100));
    assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 5, 7])), Some(&5));
}

#[test]
fn extend_merges_entries() {
    let mut trie = Poptrie::new();
    trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 8u32);

    trie.extend([
        ((u32::from_be_bytes([10, 1, 0, 0]), 16), 16u32),
    ]);

    assert_eq!(trie.len(), 2);
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 1, 1])), Some(&16));
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 2, 1, 1])), Some(&8));
}
