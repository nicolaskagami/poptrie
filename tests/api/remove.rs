use crate::u32_strides;
use poptrie::Poptrie;

#[test]
fn remove_returns_value_and_clears_lookup() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1), 6), 6);
    assert_eq!(trie.remove((u32_strides!(1), 6)), Some(6));
    assert_eq!(trie.lookup(u32_strides!(1, 63)), None);
}

#[test]
fn remove_specific_falls_back_to_less_specific() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1), 6), 6);
    trie.insert((u32_strides!(1, 1), 12), 12);
    trie.remove((u32_strides!(1, 1), 12));
    // After /12 is gone, its range falls back to /6
    assert_eq!(trie.lookup(u32_strides!(1, 1, 63)), Some(&6));
}

#[test]
fn remove_and_reinsert_gives_new_value() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1), 6), 6);
    trie.remove((u32_strides!(1), 6));
    trie.insert((u32_strides!(1), 6), 99);
    assert_eq!(trie.lookup(u32_strides!(1, 63)), Some(&99));
}

#[test]
fn removed_child_with_same_stride_doesnt_find_missing_key() {
    let prefixes = [
        ((u32::from_be_bytes([15, 0, 0, 0]), 25u8), 1),
        ((u32::from_be_bytes([8, 0, 0, 0]), 5u8), 2),
    ];

    let mut trie = Poptrie::new();
    for (p, v) in &prefixes {
        assert!(trie.insert(*p, *v).is_none());
    }

    for (p, v) in &prefixes {
        assert!(trie.contains_key(*p));
        assert_eq!(trie.remove(*p), Some(*v));
        assert!(!trie.contains_key(*p));
    }
}
