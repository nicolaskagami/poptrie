# Design
This crate implements poptrie, a compressed trie for efficient longest-prefix-match lookups.
The main use of this data structure is as a FIB (Forwarding Information Base) for IP routing.
While this problem is frequently solved with TCAMs in hardware, there is a growing need for 
software solutions with the rise of Software-Defined Networking.
This context informs a lot of our design decisions.

## Goals

- Correct, safe and portable rust
- Lookup performance
- API ergonomics

Our goal is to provide a reliable and efficient solution to LPM lookups in Rust.
This means not using `unsafe`, having few dependencies (or none, so far), and being `no_std` so that we can be used in a wide range of environments.
We currently require `alloc` but we could eventually develop our own memory management given a chunk of memory. 
It wouldn't be that far fetched as we're already very opinionated about how things are stored.

The poptrie paper provides many optimizations that are useful for performance. We implemented most of them and added a few of our own. The focus lies mostly on cache locality and reducing lookup complexity. We'll make tradeoffs that benefit lookup performance over everything, except for correctness and safety.

After those two, we'll try to make the API ergonomic, like Rust developers can expect from a map-like collection.
