use crate::u32_strides;
use poptrie::Poptrie;

#[test]
fn contains_key_true_for_inserted_prefix() {
    let mut trie = Poptrie::new();
    let prefix = (u32_strides!(1, 1,), 12);
    trie.insert(prefix, 12);
    assert!(trie.contains_key(prefix));
}

#[test]
fn contains_key_false_for_different_prefix_length() {
    let mut trie = Poptrie::new();
    let address = u32_strides!(1, 1);

    trie.insert((address, 12), 12);
    assert!(!trie.contains_key((address, 11)));
    assert!(!trie.contains_key((address, 13)));
}

#[test]
fn contains_key_false_on_empty_trie() {
    let trie = Poptrie::<(u32, u8), ()>::new();
    assert!(!trie.contains_key((0u32, 0)));
}
