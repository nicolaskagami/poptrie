use core::net::Ipv6Addr;
use std::str::FromStr;

use poptrie::{Poptrie, Prefix};

#[generic_tests::define]
mod external_prefix_types {
    use std::{any::TypeId, net::Ipv4Addr};

    use poptrie::Address;

    use super::*;

    /// We mask because cidr doesn't like non-zero bits after the mask
    fn base<A: Address + 'static>(len: u8) -> String {
        if TypeId::of::<A>() == TypeId::of::<u32>() {
            let mask = if len == 0 { 0u32 } else { u32::MAX << (32 - len) };
            let ip =
                Ipv4Addr::from_bits(u32::from_be_bytes([10, 1, 2, 3]) & mask)
                    .to_string();
            format!("{ip}/{len}")
        } else if TypeId::of::<A>() == TypeId::of::<u128>() {
            let mask = if len == 0 { 0u128 } else { u128::MAX << (128 - len) };
            let ip = Ipv6Addr::from_bits(
                u128::from_be(0x2001deadbeef1337cafefeedf00d) & mask,
            );
            format!("{ip}/{len}")
        } else {
            panic!("failed to match address type")
        }
    }

    #[test]
    fn lookup<P>()
    where
        P: Prefix + FromStr,
        P::ADDRESS: 'static,
    {
        let mut trie: Poptrie<P, u32> = Poptrie::new();
        let prefix = base::<P::ADDRESS>(8).parse::<P>().ok().unwrap();
        let shorter_prefix = base::<P::ADDRESS>(2).parse::<P>().ok().unwrap();
        let addr = prefix.address();

        // Check the shorter prefix
        trie.insert(shorter_prefix, 2);
        assert_eq!(trie.lookup(addr), Some(&2));

        // Check the longer prefix
        trie.insert(prefix, 8);
        assert_eq!(trie.lookup(addr), Some(&8));

        // Check changing the longer prefix
        assert_eq!(trie.insert(prefix, 10), Some(8));
        assert_eq!(trie.lookup(addr), Some(&10));
    }

    #[test]
    fn remove<P>()
    where
        P: Prefix + FromStr,
        P::ADDRESS: 'static,
    {
        let mut trie: Poptrie<P, u32> = Poptrie::new();
        let prefix_str = base::<P::ADDRESS>(8);

        let prefix = prefix_str.parse::<P>().ok().unwrap();
        let addr = prefix.address();

        trie.insert(prefix, 10);

        // Check removal
        assert_eq!(trie.remove(prefix), Some(10));
        assert_eq!(trie.remove(prefix), None);
        assert_eq!(trie.lookup(addr), None);
    }

    #[cfg(feature = "ipnet")]
    #[instantiate_tests(<ipnet::Ipv4Net>)]
    mod ipnet_v4 {}

    #[cfg(feature = "ipnet")]
    #[instantiate_tests(<ipnet::Ipv6Net>)]
    mod ipnet_v6 {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv4Cidr>)]
    mod cidr_v4 {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv6Cidr>)]
    mod cidr_v6 {}
}
