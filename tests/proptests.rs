//! Proptests for Poptrie
mod utils;
use core::net::Ipv4Addr;
use iptrie::Poptrie;
use iptrie::Prefix;
use proptest::prelude::*;
use utils::Ipv4Prefix;

use crate::utils::HashMapLpm;

/// Generate arbitrary IPv4 addresses
fn ipv4_strategy() -> impl Strategy<Value = Ipv4Addr> {
    any::<u32>().prop_map(Ipv4Addr::from_bits)
}

/// Generate arbitrary prefix lengths (0-32)
fn prefix_len_strategy() -> impl Strategy<Value = u8> {
    0u8..=32
}

/// Generate arbitrary IPv4 prefixes
fn ipv4_prefix_strategy() -> impl Strategy<Value = Ipv4Prefix> {
    (ipv4_strategy(), prefix_len_strategy())
        .prop_map(|(addr, prefix_len)| Ipv4Prefix::new(addr, prefix_len))
}

/// Generate a vector of IPv4 prefixes with associated values
fn prefix_value_vec_strategy<T: Clone + std::fmt::Debug>(
    value_strategy: impl Strategy<Value = T>,
    max_size: usize,
) -> impl Strategy<Value = Vec<(Ipv4Prefix, T)>> {
    prop::collection::vec((ipv4_prefix_strategy(), value_strategy), 0..=max_size)
}

proptest! {
    /// Test that Poptrie matches reference implementation
    #[test]
    fn matches_reference_model(
        prefixes in prefix_value_vec_strategy(any::<u32>(), 50),
        lookup_ips in prop::collection::vec(ipv4_strategy(), 1..=20)
    ) {
        let mut poptrie = Poptrie::new();
        let mut reference = HashMapLpm::new();

        // Insert all prefixes into both implementations
        for (prefix, value) in &prefixes {
            poptrie.insert(Prefix(prefix.addr.to_bits(),prefix.prefix_len), *value);
            reference.insert(prefix.addr.clone(), prefix.prefix_len, *value);
        }

        // Compare lookups
        for ip in lookup_ips {
            let trie_result = poptrie.lookup(ip.to_bits());
            let ref_result = reference.lookup(ip);

            prop_assert_eq!(
                trie_result,
                ref_result,
                "Mismatch for IP {}: trie={:?}, reference={:?}",
                ip,
                trie_result,
                ref_result
            );
        }
    }
}
