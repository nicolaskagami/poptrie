Poptrie
====
A pure Rust implementation of [Poptrie](https://dl.acm.org/doi/abs/10.1145/2829988.2787474), a data structure for efficient longest-prefix matching (LPM) lookups.

Poptrie uses bitmaps combined with the popcount instruction to achieve very fast longest-prefix lookups. 
During lookup, the key is consumed in the biggest step that can be represented in a bitmap for which the native popcount instruction exists (i.e. 6-bit steps in a 64-bit bitmap).
It is similar to how a tree-bitmap works, but with a more contiguous use of memory, trading insertion speed for cache locality.

This is particularly useful for IP forwarding tables (FIBs), where the longest-prefix matching is a common operation and insertions are comparatively rare.

[![CI](https://github.com/nicolaskagami/poptrie/actions/workflows/ci.yml/badge.svg)](https://github.com/nicolaskagami/poptrie/actions)
[![Crates.io](https://img.shields.io/crates/v/poptrie)](https://crates.io/crates/poptrie)
[![Docs.rs](https://docs.rs/poptrie/badge.svg)](https://docs.rs/poptrie)
[![MIT licensed](https://img.shields.io/badge/license-MIT-blue)](LICENSE-MIT)
[![Apache 2.0 licensed](https://img.shields.io/badge/license-Apache--2.0-blue)](LICENSE-APACHE)

### Features

- Pure rust, `no_std`, no external dependencies, no `unsafe` code. Does require `alloc`.
- Native support for `ipnet`, `cidr`, and `(K, u8)` for `IpAddr` and all unsigned integers.
- Supports *very fast* `lookup()` operations while still being ergonomic, safe and readable.
- Supports common collection methods such as `insert()`, `remove()`, `keys()`, `values()`, etc.
- Supports fast construction with `FromIterator` and the ergonomic `IntoIter` patterns.

## Usage

### Installation

```bash
cargo add poptrie
```
### Example

``` rust
use poptrie::Poptrie;
use core::net::Ipv4Addr;

// Create a routing table for IPv4 addresses
let mut trie = Poptrie::<_, &str>::new();

// Insert prefixes with their associated values
trie.insert((Ipv4Addr::from([192, 168, 0, 0]), 16), "16");
trie.insert((Ipv4Addr::from([192, 168, 1, 0]), 24), "24");
trie.insert((Ipv4Addr::from([10, 0, 0, 0]), 8), "8");

// Longest prefix match — 192.168.1.x matches the more specific /24
assert_eq!(trie.lookup(Ipv4Addr::from([192, 168, 1, 5])), Some(&"24"));
assert_eq!(trie.lookup(Ipv4Addr::from([192, 168, 2, 5])), Some(&"16"));
assert_eq!(trie.lookup(Ipv4Addr::from([8, 8, 8, 8])), None);

// Check and remove a prefix
assert!(trie.contains_key((Ipv4Addr::from([192, 168, 1, 0]), 24)));
trie.remove((Ipv4Addr::from([192, 168, 1, 0]), 24));

// 192.168.1.x now falls back to the /16
assert_eq!(trie.lookup(Ipv4Addr::from([192, 168, 1, 5])), Some(&"16"));
```

### API

| Function | Description | Complexity  |
|---|---|---|
| `new()` | Construct a new, empty poptrie | `O(1)` |
| `lookup(address)` | Longest-prefix match lookup, returns `Option<&V>` | `O(1)`*  |
| `insert(prefix, value)` | Insert/replace a value for an exact prefix, returning the previous value if present | `O(n)`** |
| `contains_key(prefix)` | Returns `true` if the exact prefix is present | `O(1)` |
| `remove(prefix)` | Remove an exact prefix and return its value, if present | `O(n)` |

> \* Lookups are technically constant w.r.t. `n` (number of entries). However, cache locality inevitably degrades with scale.

> \** Inserts are `O(n)` since all the nodes are compacted into a contiguous space.

### Lookup performance

This crate's lookup performance beats other trie-based implementations, including the original poptrie ([pixos/poptrie](https://github.com/pixos/poptrie)).

Benchmarked with random lookups on tables of 1k, 10k and 100k random prefixes. 
All contenders were built with `RUSTFLAGS="-C target-cpu=native"`, which enables the use of architecture-specific instructions, if available. 
This is critical for performance as the poptrie relies on native `POPCNT` and bit manipulation instructions (e.g. `BEXTR` on x86) to achieve its performance characteristics.

| Implementation | 1k prefixes | 10k prefixes | 100k prefixes |
|---|---|---|---|
| **nicolaskagami/poptrie** (this crate) | 461.89 Mlookups/s | 324.56 Mlookups/s | 175.44 Mlookups/s |
| [pixos/poptrie](https://github.com/pixos/poptrie) (with Rust bindings) | 400.93 Mlookups/s | 332.54 Mlookups/s | 166.75 Mlookups/s |
| [tiborschneider/prefix-trie](https://github.com/tiborschneider/prefix-trie) | 300.95 Mlookups/s | 296.49 Mlookups/s | 110.92 Mlookups/s |
| [oxidecomputer/poptrie](https://github.com/oxidecomputer/poptrie) | 309.60 Mlookups/s | 212.84 Mlookups/s | 95.01 Mlookups/s |

> Benchmarked on an AMD Ryzen 9 7900 (12-core, x86_64), Linux kernel 6.18, rustc 1.93.1.

Running the benchmarks:

``` bash
RUSTFLAGS="-C target-cpu=native" cargo bench
```

### Reference 

Asai, Hirochika, and Yasuhiro Ohara. **[Poptrie: A Compressed Trie with Population Count for Fast and Scalable Software IP Routing Table Lookup](https://doi.org/10.1145/2829988.2787474)** ACM SIGCOMM Computer Communication Review 45.4 (2015): 57-70.

### License 

This project is licensed under either of:

- [MIT License](LICENSE-MIT)
- [Apache License, Version 2.0](LICENSE-APACHE)
