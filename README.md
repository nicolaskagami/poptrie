Poptrie
====
A pure Rust implementation of [Poptrie](https://dl.acm.org/doi/10.1145/2740070.2626377), a data structure for efficient longest-prefix matching (LPM) lookups.

Poptrie uses bitmaps combined with popcount to achieve fast IP routing table lookups with high cache locality. During lookup, the key is consumed in the biggest step that can be represented in a bitmap for which the native popcount instruction exists (i.e. 6-bit steps in a 64-bit bitmap).

![CI](https://github.com/nicolaskagami/poptrie/actions/workflows/ci.yml/badge.svg)

### Features

- Pure rust, `no_std`, no external dependencies, no `unsafe` code. 
- Generic over key type (e.g. `u32` for IPv4, `u128` for IPv6).
- Supports insertion, deletion, contains, and lookup operations.

## Installation

```toml
[dependencies]
poptrie = { git = "https://github.com/nicolaskagami/poptrie" }
```
### Example

``` rust
use poptrie::Poptrie;

// Create a routing table for IPv4 addresses
let mut trie = Poptrie::<u32, &str>::new();

// Insert prefixes with their associated values
trie.insert(u32::from_be_bytes([192, 168, 0, 0]), 16, "192.168.0.0/16");
trie.insert(u32::from_be_bytes([192, 168, 1, 0]), 24, "192.168.1.0/24");
trie.insert(u32::from_be_bytes([10, 0, 0, 0]), 8, "10.0.0.0/8");

// Longest prefix match — 192.168.1.x matches the more specific /24
assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 1, 5])), Some(&"192.168.1.0/24"));
assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 2, 5])), Some(&"192.168.0.0/16"));
assert_eq!(trie.lookup(u32::from_be_bytes([8, 8, 8, 8])), None);

// Check and remove a prefix
assert!(trie.contains_key(u32::from_be_bytes([192, 168, 1, 0]), 24));
trie.remove(u32::from_be_bytes([192, 168, 1, 0]), 24);

// 192.168.1.x now falls back to the /16
assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 1, 5])), Some(&"192.168.0.0/16"));
```

### API

| Function | Description |
|---|---|
| `Poptrie::new()` | Construct a new, empty poptrie |
| `insert(key, key_length, value)` | Insert a value associated with the given prefix |
| `lookup(key)` | Longest-prefix match lookup, returns `Option<&V>` |
| `contains_key(key, key_length)` | Returns `true` if the exact prefix is present |
| `remove(key, key_length)` | Remove a prefix and return its value |### License

### Reference 

Hirochika Asai and Yasuhiro Ohara. 2015. **[Poptrie: A Compressed Trie with Population Count for Fast and Scalable Software IP Routing Table Lookup](https://doi.org/10.1145/2740070.2626377)**. In *Proceedings of the 2015 ACM Conference on Special Interest Group on Data Communication* (SIGCOMM '15). ACM, New York, NY, USA, 57–70.


### License 

This project is licensed under either of:

- [MIT License](LICENSE-MIT)
- [Apache License, Version 2.0](LICENSE-APACHE)
