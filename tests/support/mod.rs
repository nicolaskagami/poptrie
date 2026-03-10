use core::net::Ipv6Addr;

use poptrie::Poptrie;

fn ip6(s: &str) -> u128 {
    u128::from(s.parse::<Ipv6Addr>().unwrap())
}

#[test]
fn ipv6_basic_lookup() {
    let mut trie = Poptrie::new();
    trie.insert((ip6("2001:db8::"), 32), 32u32);
    assert_eq!(trie.lookup(ip6("2001:db8::1")), Some(&32));
    assert_eq!(trie.lookup(ip6("2001:db9::1")), None);
}

#[test]
fn ipv6_lpm_selects_most_specific() {
    let mut trie = Poptrie::new();
    trie.insert((ip6("2001:db8::"), 32), 32u32);
    trie.insert((ip6("2001:db8:dead::"), 48), 48u32);

    assert_eq!(trie.lookup(ip6("2001:db8:dead::1")), Some(&48));
    assert_eq!(trie.lookup(ip6("2001:db8:beef::1")), Some(&32));
    assert_eq!(trie.lookup(ip6("2001:db9::")), None);
}

#[test]
fn ipv6_default_route() {
    let mut trie = Poptrie::new();
    trie.insert((ip6("::"), 0), 0u32);
    trie.insert((ip6("2001:db8::"), 32), 32u32);

    assert_eq!(trie.lookup(ip6("2001:db8::1")), Some(&32));
    assert_eq!(trie.lookup(ip6("fe80::1")), Some(&0));
    assert_eq!(trie.lookup(ip6("::1")), Some(&0));
}

#[test]
fn ipv6_remove_falls_back_to_less_specific() {
    let mut trie = Poptrie::new();
    trie.insert((ip6("2001:db8::"), 32), 32u32);
    trie.insert((ip6("2001:db8:dead::"), 48), 48u32);
    trie.remove((ip6("2001:db8:dead::"), 48));

    assert_eq!(trie.lookup(ip6("2001:db8:dead::1")), Some(&32));
}

#[test]
fn ipv6_host_route() {
    let mut trie = Poptrie::new();
    trie.insert((ip6("::1"), 128), 128u32);
    assert_eq!(trie.lookup(ip6("::1")), Some(&128));
    assert_eq!(trie.lookup(ip6("::2")), None);
}
