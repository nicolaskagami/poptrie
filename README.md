Poptrie
====
A pure Rust implementation of a Poptrie, a data structure for efficient longest-prefix matching lookups.

### Reference 
Based on “Poptrie: A Compressed Trie with Population Count for Fast and Scalable Software IP Routing Table Lookup” by Hirochika Asai and Yasuhiro Ohara.

### License
This work is dual-licensed under the MIT License and the Apache License, Version 2.0.

### Example

``` rust
use poptrie::Poptrie;

// Create a routing table for IPv4 addresses
let mut trie = Poptrie::<u32, &str>::new();

// Insert prefixes with their associated values
trie.insert(u32::from_be_bytes([192, 168, 0, 0]), 16, "192.168.0.0/16");
trie.insert(u32::from_be_bytes([192, 168, 1, 0]), 24, "192.168.1.0/24");
trie.insert(u32::from_be_bytes([10, 0, 0, 0]),8, "10.0.0.0/8");

// Perform longest prefix match lookups
assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 1, 5])), Some("192.168.1.0/24"));
assert_eq!(trie.lookup(u32::from_be_bytes([192, 168, 2, 5])), Some("192.168.0.0/16"));
assert_eq!(trie.lookup(u32::from_be_bytes([10, 1, 2, 3])), Some("10.0.0.0/8"));
assert_eq!(trie.lookup(u32::from_be_bytes([8, 8, 8, 8])), None);
```
