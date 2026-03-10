use crate::u32_strides;
use poptrie::Poptrie;

#[test]
fn default_route_matches_everything() {
    let mut trie = Poptrie::new();
    trie.insert((0u32, 0), 0);
    assert_eq!(trie.lookup(0u32), Some(&0));
    assert_eq!(trie.lookup(u32::MAX), Some(&0));
    assert_eq!(trie.lookup(u32_strides!(1, 2, 3, 4)), Some(&0));
}

#[test]
fn specific_prefix_overrides_default_route() {
    let mut trie = Poptrie::new();
    trie.insert((0u32, 0), 0);
    trie.insert((u32_strides!(1), 6), 1);
    // Inside the /6 prefix
    assert_eq!(trie.lookup(u32_strides!(1, 2)), Some(&1));
    // Outside — falls back to default
    assert_eq!(trie.lookup(u32_strides!(2)), Some(&0));
}

#[test]
fn default_route_overwrite_propagates_to_children() {
    let mut trie = Poptrie::new();
    trie.insert((0u32, 0), 0);
    trie.insert((u32_strides!(1, 1), 15), 2);
    // Overwrite the default
    trie.insert((0u32, 0), 1);
    // The /15 child is still there
    assert_eq!(trie.lookup(u32_strides!(1, 1)), Some(&2));
    // Everything else now uses the new default
    assert_eq!(trie.lookup(u32_strides!(1, 1, 32)), Some(&1));
}

#[test]
fn default_at_first_level_propagates_into_second_level() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(1), 6), 6);
    trie.insert((0, 12), 12);
    // The /6 is shallower and its stride doesn't overlap with /12's stride
    assert_eq!(trie.lookup(u32_strides!(1)), Some(&6));
}

#[test]
fn default_at_second_level_propagates_into_third_level() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(0, 1), 12), 12);
    trie.insert((0, 18), 18);
    assert_eq!(trie.lookup(u32_strides!(0, 1)), Some(&12));
}

#[test]
fn non_full_length_default_does_not_cover_sibling_subtree() {
    let mut trie = Poptrie::new();
    trie.insert((u32_strides!(0b001100), 10), 10);
    trie.insert((0, 1), 1);
    // This address shares the first stride's leading bit with /1 but not /10
    assert_eq!(trie.lookup(u32_strides!(0b001100, 0b000100)), Some(&1));
}
