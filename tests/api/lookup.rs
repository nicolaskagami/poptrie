use crate::u32_strides;
use poptrie::Poptrie;

#[test]
fn empty_trie_returns_none() {
    let trie = Poptrie::<(u32, u8), ()>::new();
    assert_eq!(trie.lookup(0u32), None);
    assert_eq!(trie.lookup(u32::MAX), None);
}

#[test]
fn prefix_at_first_stride_boundary() {
    // /6: the entire first stride
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1), 6), 6);
    assert_eq!(trie.lookup(u32_strides!(1, 63)), Some(&6));
    assert_eq!(trie.lookup(u32_strides!(2)), None);
}

#[test]
fn prefix_at_second_stride_boundary() {
    // /12: exactly two strides consumed
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1, 1), 12), 12);
    assert_eq!(trie.lookup(u32_strides!(1, 1, 63)), Some(&12));
    assert_eq!(trie.lookup(u32_strides!(1, 2)), None);
}

#[test]
fn prefix_spanning_two_stride_levels() {
    // /7: one full stride (6 bits) plus 1 bit into the next
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1), 7), 7);
    // Same first stride, second bit of second stride = 0 → match
    assert_eq!(trie.lookup(u32_strides!(1, 31)), Some(&7));
    // Second bit of second stride = 1 → no match
    assert_eq!(trie.lookup(u32_strides!(1, 32)), None);
}

#[test]
fn lpm_selects_longest_matching_prefix() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1), 6), 6);
    trie.insert((u32_strides!(1, 1), 12), 12);
    trie.insert((u32_strides!(1, 1, 1), 18), 18);

    // Matches /18
    assert_eq!(trie.lookup(u32_strides!(1, 1, 1, 63)), Some(&18));
    // /18 prefix doesn't match, falls back to /12
    assert_eq!(trie.lookup(u32_strides!(1, 1, 2)), Some(&12));
    // /12 prefix doesn't match, falls back to /6
    assert_eq!(trie.lookup(u32_strides!(1, 2)), Some(&6));
    // Nothing matches
    assert_eq!(trie.lookup(u32_strides!(2)), None);
}

#[test]
fn lpm_sibling_strides_do_not_bleed() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1), 12), 1);
    trie.insert((u32_strides!(1, 2), 12), 2);

    assert_eq!(trie.lookup(u32_strides!(1, 0, 63)), Some(&1));
    assert_eq!(trie.lookup(u32_strides!(1, 2, 63)), Some(&2));
    // Different first stride — no match
    assert_eq!(trie.lookup(u32_strides!(1, 3)), None);
}

#[test]
fn lpm_child_prefix_inserted_before_parent() {
    // Insert deeper prefix first, shallower prefix second
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1, 1), 13), 13);
    trie.insert((u32_strides!(1), 12), 12);
    trie.insert((u32_strides!(1), 7), 7);
    // Address outside all three prefixes
    assert_eq!(trie.lookup(u32_strides!(1, 33, 32)), None);
}

#[test]
fn two_prefixes_one_stride_apart_with_shared_parent() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1, 1, 1, 1), 25), 25);
    trie.insert((u32_strides!(1, 1, 1, 1, 3, 1), 32), 32);
    assert_eq!(trie.lookup(u32_strides!(1, 1, 1, 1, 1)), Some(&25));
    assert_eq!(trie.lookup(u32_strides!(1, 1, 1, 1, 3, 1)), Some(&32));
}
