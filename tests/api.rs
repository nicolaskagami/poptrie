use core::net::Ipv6Addr;

use poptrie::Poptrie;

// Stride boundaries are every 6 bits, visible in binary literals as groups:
// 0b XXXXXX_XXXXXX_XXXXXX_XXXXXX_XXXXXX_XX
//    stride1 stride2 stride3 stride4 stride5 remainder(2)

// -------------------------------------------------------------------------
// Empty trie
// -------------------------------------------------------------------------

#[test]
fn empty_trie_returns_none() {
    let trie = Poptrie::<u32, ()>::new();
    assert_eq!(trie.lookup(0u32), None);
    assert_eq!(trie.lookup(u32::MAX), None);
}

// -------------------------------------------------------------------------
// Default route (0-length prefix / catch-all)
// -------------------------------------------------------------------------

#[test]
fn default_route_matches_everything() {
    let mut trie = Poptrie::new();
    trie.insert(0u32, 0, 0);
    assert_eq!(trie.lookup(0u32), Some(&0));
    assert_eq!(trie.lookup(u32::MAX), Some(&0));
    assert_eq!(
        trie.lookup(0b111111_000000_000000_000000_000000_00u32),
        Some(&0)
    );
}

#[test]
fn specific_prefix_overrides_default_route() {
    let mut trie = Poptrie::new();
    trie.insert(0u32, 0, 0);
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 6, 1);
    // Inside the /6 prefix
    assert_eq!(
        trie.lookup(0b000001_111111_000000_000000_000000_00u32),
        Some(&1)
    );
    // Outside — falls back to default
    assert_eq!(
        trie.lookup(0b000010_000000_000000_000000_000000_00u32),
        Some(&0)
    );
}

#[test]
fn default_route_overwrite_propagates_to_children() {
    let mut trie = Poptrie::new();
    trie.insert(0u32, 0, 0);
    trie.insert(0b000001_000001_000000_000000_000000_00u32, 15, 2);
    // Overwrite the default
    trie.insert(0u32, 0, 1);
    // The /15 child is still there
    assert_eq!(
        trie.lookup(0b000001_000001_000000_000000_000000_00u32),
        Some(&2)
    );
    // Everything else now uses the new default
    assert_eq!(
        trie.lookup(0b000001_000001_001000_000000_000000_00u32),
        Some(&1)
    );
}

// -------------------------------------------------------------------------
// Single prefix at each stride boundary
// -------------------------------------------------------------------------

#[test]
fn prefix_at_first_stride_boundary() {
    // /6: the entire first stride
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 6, 6);
    assert_eq!(
        trie.lookup(0b000001_111111_000000_000000_000000_00u32),
        Some(&6)
    );
    assert_eq!(trie.lookup(0b000010_000000_000000_000000_000000_00u32), None);
}

#[test]
fn prefix_at_second_stride_boundary() {
    // /12: exactly two strides consumed
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000001_000000_000000_000000_00u32, 12, 12);
    assert_eq!(
        trie.lookup(0b000001_000001_111111_000000_000000_00u32),
        Some(&12)
    );
    assert_eq!(trie.lookup(0b000001_000010_000000_000000_000000_00u32), None);
}

#[test]
fn prefix_spanning_two_stride_levels() {
    // /7: one full stride (6 bits) plus 1 bit into the next
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 7, 7);
    // Same first stride, second bit of second stride = 0 → match
    assert_eq!(
        trie.lookup(0b000001_011111_000000_000000_000000_00u32),
        Some(&7)
    );
    // Second bit of second stride = 1 → no match
    assert_eq!(trie.lookup(0b000001_100000_000000_000000_000000_00u32), None);
}

// -------------------------------------------------------------------------
// LPM: most-specific match wins across multiple stride levels
// -------------------------------------------------------------------------

#[test]
fn lpm_selects_deepest_matching_prefix() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 6, 6);
    trie.insert(0b000001_000001_000000_000000_000000_00u32, 12, 12);
    trie.insert(0b000001_000001_000001_000000_000000_00u32, 18, 18);

    // Matches /18
    assert_eq!(
        trie.lookup(0b000001_000001_000001_111111_000000_00u32),
        Some(&18)
    );
    // /18 prefix doesn't match, falls back to /12
    assert_eq!(
        trie.lookup(0b000001_000001_000010_000000_000000_00u32),
        Some(&12)
    );
    // /12 prefix doesn't match, falls back to /6
    assert_eq!(
        trie.lookup(0b000001_000010_000000_000000_000000_00u32),
        Some(&6)
    );
    // Nothing matches
    assert_eq!(trie.lookup(0b000010_000000_000000_000000_000000_00u32), None);
}

#[test]
fn lpm_sibling_strides_do_not_bleed() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 12, 1);
    trie.insert(0b000001_000010_000000_000000_000000_00u32, 12, 2);

    assert_eq!(
        trie.lookup(0b000001_000000_111111_000000_000000_00u32),
        Some(&1)
    );
    assert_eq!(
        trie.lookup(0b000001_000010_111111_000000_000000_00u32),
        Some(&2)
    );
    // Different first stride — no match
    assert_eq!(trie.lookup(0b000001_000011_000000_000000_000000_00u32), None);
}

#[test]
fn lpm_child_prefix_inserted_before_parent() {
    // Insert deeper prefix first, shallower prefix second
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000001_000000_000000_000000_00u32, 13, 13);
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 12, 12);
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 7, 7);
    // Address outside all three prefixes
    assert_eq!(trie.lookup(0b000001_100001_100000_000000_000000_00u32), None);
}

// -------------------------------------------------------------------------
// Prefixes sharing a parent stride node
// -------------------------------------------------------------------------

#[test]
fn two_prefixes_one_stride_apart_with_shared_parent() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000001_000001_000001_000000_00u32, 25, 25);
    trie.insert(0b000001_000001_000001_000001_000011_01u32, 32, 32);
    assert_eq!(
        trie.lookup(0b000001_000001_000001_000001_000001_00u32),
        Some(&25)
    );
    assert_eq!(
        trie.lookup(0b000001_000001_000001_000001_000011_01u32),
        Some(&32)
    );
}

// -------------------------------------------------------------------------
// Default propagation into newly created child nodes
// -------------------------------------------------------------------------

#[test]
fn default_at_first_level_propagates_into_second_level_node() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 6, 6);
    trie.insert(0b000000_000000_000000_000000_000000_00u32, 12, 12);
    // The /6 is shallower and its stride doesn't overlap with /12's stride
    assert_eq!(
        trie.lookup(0b000001_000000_000000_000000_000000_00u32),
        Some(&6)
    );
}

#[test]
fn default_at_second_level_propagates_into_third_level_node() {
    let mut trie = Poptrie::new();
    trie.insert(0b000000_110000_000000_000000_000000_00u32, 12, 12);
    trie.insert(0b000000_000000_000000_000000_000000_00u32, 18, 18);
    assert_eq!(
        trie.lookup(0b000000_110000_000000_000000_000000_00u32),
        Some(&12)
    );
}

#[test]
fn non_full_length_default_does_not_cover_sibling_subtree() {
    let mut trie = Poptrie::new();
    trie.insert(0b001100_000000_000000_000000_000000_00u32, 10, 10);
    trie.insert(0b000000_000000_000000_000000_000000_00u32, 1, 1);
    // This address shares the first stride's leading bit with /1 but not /10
    assert_eq!(
        trie.lookup(0b001100_000100_000000_000000_000000_00u32),
        Some(&1)
    );
}

// -------------------------------------------------------------------------
// contains_key
// -------------------------------------------------------------------------

#[test]
fn contains_key_true_for_inserted_prefix() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000001_000000_000000_000000_00u32, 12, 12);
    assert!(trie.contains_key(0b000001_000001_000000_000000_000000_00u32, 12));
}

#[test]
fn contains_key_false_for_different_prefix_length() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000001_000000_000000_000000_00u32, 12, 12);
    assert!(!trie.contains_key(0b000001_000001_000000_000000_000000_00u32, 11));
    assert!(!trie.contains_key(0b000001_000001_000000_000000_000000_00u32, 13));
}

#[test]
fn contains_key_false_on_empty_trie() {
    let trie = Poptrie::<u32, ()>::new();
    assert!(!trie.contains_key(0u32, 0));
}

// -------------------------------------------------------------------------
// remove
// -------------------------------------------------------------------------

#[test]
fn remove_returns_value_and_clears_lookup() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 6, 6);
    assert_eq!(
        trie.remove(0b000001_000000_000000_000000_000000_00u32, 6),
        Some(6)
    );
    assert_eq!(trie.lookup(0b000001_111111_000000_000000_000000_00u32), None);
}

#[test]
fn remove_specific_falls_back_to_less_specific() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 6, 6);
    trie.insert(0b000001_000001_000000_000000_000000_00u32, 12, 12);
    trie.remove(0b000001_000001_000000_000000_000000_00u32, 12);
    // After /12 is gone, its range falls back to /6
    assert_eq!(
        trie.lookup(0b000001_000001_111111_000000_000000_00u32),
        Some(&6)
    );
}

#[test]
fn remove_and_reinsert_gives_new_value() {
    let mut trie = Poptrie::new();
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 6, 6);
    trie.remove(0b000001_000000_000000_000000_000000_00u32, 6);
    trie.insert(0b000001_000000_000000_000000_000000_00u32, 6, 99);
    assert_eq!(
        trie.lookup(0b000001_111111_000000_000000_000000_00u32),
        Some(&99)
    );
}

// -------------------------------------------------------------------------
// Insert order independence
// -------------------------------------------------------------------------

#[test]
fn insert_order_does_not_affect_lpm() {
    let mut forward = Poptrie::new();
    forward.insert(0b000001_000000_000000_000000_000000_00u32, 6, 6);
    forward.insert(0b000001_000001_000000_000000_000000_00u32, 12, 12);
    forward.insert(0b000001_000001_000001_000000_000000_00u32, 18, 18);

    let mut reverse = Poptrie::new();
    reverse.insert(0b000001_000001_000001_000000_000000_00u32, 18, 18);
    reverse.insert(0b000001_000001_000000_000000_000000_00u32, 12, 12);
    reverse.insert(0b000001_000000_000000_000000_000000_00u32, 6, 6);

    let lookups = [
        0b000001_000001_000001_111111_000000_00u32,
        0b000001_000001_000010_000000_000000_00u32,
        0b000001_000010_000000_000000_000000_00u32,
        0b000010_000000_000000_000000_000000_00u32,
    ];
    for addr in lookups {
        assert_eq!(forward.lookup(addr), reverse.lookup(addr),);
    }
}

// -------------------------------------------------------------------------
// IPv6 (u128)
// -------------------------------------------------------------------------

fn ip6(s: &str) -> u128 {
    u128::from(s.parse::<Ipv6Addr>().unwrap())
}

#[test]
fn ipv6_basic_lookup() {
    let mut trie = Poptrie::new();
    trie.insert(ip6("2001:db8::"), 32, 32u32);
    assert_eq!(trie.lookup(ip6("2001:db8::1")), Some(&32));
    assert_eq!(trie.lookup(ip6("2001:db9::1")), None);
}

#[test]
fn ipv6_lpm_selects_most_specific() {
    let mut trie = Poptrie::new();
    trie.insert(ip6("2001:db8::"), 32, 32u32);
    trie.insert(ip6("2001:db8:dead::"), 48, 48u32);

    assert_eq!(trie.lookup(ip6("2001:db8:dead::1")), Some(&48));
    assert_eq!(trie.lookup(ip6("2001:db8:beef::1")), Some(&32));
    assert_eq!(trie.lookup(ip6("2001:db9::")), None);
}

#[test]
fn ipv6_default_route() {
    let mut trie = Poptrie::new();
    trie.insert(ip6("::"), 0, 0u32);
    trie.insert(ip6("2001:db8::"), 32, 32u32);

    assert_eq!(trie.lookup(ip6("2001:db8::1")), Some(&32));
    assert_eq!(trie.lookup(ip6("fe80::1")), Some(&0));
    assert_eq!(trie.lookup(ip6("::1")), Some(&0));
}

#[test]
fn ipv6_remove_falls_back_to_less_specific() {
    let mut trie = Poptrie::new();
    trie.insert(ip6("2001:db8::"), 32, 32u32);
    trie.insert(ip6("2001:db8:dead::"), 48, 48u32);
    trie.remove(ip6("2001:db8:dead::"), 48);

    assert_eq!(trie.lookup(ip6("2001:db8:dead::1")), Some(&32));
}

#[test]
fn ipv6_host_route() {
    let mut trie = Poptrie::new();
    trie.insert(ip6("::1"), 128, 128u32);
    assert_eq!(trie.lookup(ip6("::1")), Some(&128));
    assert_eq!(trie.lookup(ip6("::2")), None);
}
