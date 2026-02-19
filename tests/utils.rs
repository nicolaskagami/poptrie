use std::collections::HashMap;
use std::net::Ipv4Addr;

/// Reference `HashMap` implementation for LPM
// TODO: Generify to K
pub struct HashMapLpm<T> {
    map: HashMap<(Ipv4Addr, u8), T>,
}

impl<T> HashMapLpm<T>
where
    T: Copy,
{
    pub fn new() -> Self {
        HashMapLpm { map: HashMap::new() }
    }

    pub fn lookup(&self, address: Ipv4Addr) -> Option<&T> {
        // Check all prefix lengths starting with the longest.
        for length in (0..=32).rev() {
            // Apply the mask to the address
            let masked_prefix = mask_prefix(address, length);
            // Return on the first match
            if let Some(result) = self.map.get(&(masked_prefix, length)) {
                return Some(result);
            }
        }
        None
    }

    pub fn insert(&mut self, prefix: Ipv4Addr, prefix_length: u8, value: T) {
        let masked_prefix = mask_prefix(prefix, prefix_length);
        self.map.insert((masked_prefix, prefix_length), value);
    }
}

/// Mask the `address` with the given `prefix_length`
fn mask_prefix(addr: Ipv4Addr, prefix_len: u8) -> Ipv4Addr {
    debug_assert!(prefix_len <= 32);
    let mask =
        if prefix_len == 0 { 0u32 } else { u32::MAX << (32 - prefix_len) };
    Ipv4Addr::from_bits(addr.to_bits() & mask)
}
/// Represents an IPv4 prefix (CIDR notation)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ipv4Prefix {
    pub addr: Ipv4Addr,
    pub prefix_len: u8,
}

impl Ipv4Prefix {
    pub fn new(addr: Ipv4Addr, prefix_len: u8) -> Self {
        Self { addr: mask_prefix(addr, prefix_len), prefix_len }
    }
}
