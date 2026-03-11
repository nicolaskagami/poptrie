use core::net::{Ipv4Addr, Ipv6Addr};

use crate::address::Address;

/// A prefix is a pattern to match the beginning of a sequence, in this case called an
/// `ADDRESS`. The prefix is represented by an `ADDRESS` and a `prefix_length` that
/// defines the number of bits in the prefix (counted from the most significant bits).
///
/// # Examples
///
/// ```
/// use poptrie::{Poptrie, Prefix};
///
/// let mut trie = Poptrie::<(u32, u8), &str>::new();
/// trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), "10/8");
/// assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 2, 3])), Some(&"10/8"));
/// ```
///
/// Implementing `Prefix` for a custom type:
/// ```
/// use poptrie::{Prefix};
///
/// #[derive(Clone, Copy, PartialEq, Eq)]
/// struct Ipv4Net { addr: u32, len: u8 }
///
/// impl Prefix for Ipv4Net {
///     type ADDRESS = u32;
///     fn address(&self) -> u32 { self.addr }
///     fn prefix_length(&self) -> u8 { self.len }
/// }
/// ```
pub trait Prefix: Copy {
    /// The underlying address type.
    type ADDRESS: Address;

    /// Returns the address part of the prefix.
    fn address(&self) -> Self::ADDRESS;

    /// Returns the prefix length (number of significant bits).
    fn prefix_length(&self) -> u8;
}

impl<A: Address> Prefix for (A, u8) {
    type ADDRESS = A;

    #[inline(always)]
    fn address(&self) -> Self::ADDRESS {
        self.0
    }

    #[inline(always)]
    fn prefix_length(&self) -> u8 {
        self.1
    }
}

impl Prefix for (Ipv4Addr, u8) {
    type ADDRESS = u32;

    #[inline(always)]
    fn address(&self) -> Self::ADDRESS {
        self.0.to_bits()
    }

    #[inline(always)]
    fn prefix_length(&self) -> u8 {
        self.1
    }
}

impl Prefix for (Ipv6Addr, u8) {
    type ADDRESS = u128;

    #[inline(always)]
    fn address(&self) -> Self::ADDRESS {
        self.0.to_bits()
    }

    #[inline(always)]
    fn prefix_length(&self) -> u8 {
        self.1
    }
}

#[cfg(feature = "ipnet")]
impl Prefix for ipnet::Ipv4Net {
    type ADDRESS = u32;

    #[inline(always)]
    fn address(&self) -> Self::ADDRESS {
        u32::from(self.network())
    }

    #[inline(always)]
    fn prefix_length(&self) -> u8 {
        self.prefix_len()
    }
}

#[cfg(feature = "ipnet")]
impl Prefix for ipnet::Ipv6Net {
    type ADDRESS = u128;

    #[inline(always)]
    fn address(&self) -> Self::ADDRESS {
        u128::from(self.network())
    }

    #[inline(always)]
    fn prefix_length(&self) -> u8 {
        self.prefix_len()
    }
}

#[cfg(feature = "cidr")]
impl Prefix for cidr::Ipv4Cidr {
    type ADDRESS = u32;

    #[inline(always)]
    fn address(&self) -> Self::ADDRESS {
        self.first_address().into()
    }

    #[inline(always)]
    fn prefix_length(&self) -> u8 {
        self.network_length()
    }
}

#[cfg(feature = "cidr")]
impl Prefix for cidr::Ipv6Cidr {
    type ADDRESS = u128;

    #[inline(always)]
    fn address(&self) -> Self::ADDRESS {
        self.first_address().into()
    }

    #[inline(always)]
    fn prefix_length(&self) -> u8 {
        self.network_length()
    }
}
