# Comparison
This document compares `nicolaskagami/poptrie` with a few similar crates, namely two other implementations of poptrie and a prominent prefix trie implementation. Wherever performance comparisons are made, these were informed by a dedicated benchmarking approach described in [BENCHMARKS](BENCHMARKS.md).

## `tiborschneider/prefix-trie`
[tiborschneider/prefix-trie](https://github.com/tiborschneider/prefix-trie)'s `PrefixMap` offers very similar functionality to this crate. Our internal approach is different, however, as we implement the poptrie algorithm, making use of native popcount instructions for very efficient longest prefix matching.

Compared to it, this crate has the following advantages:
- Better lookup performance (about 50% more lookups/sec)
  - This is our main design goal and likely what you should care about if implementing a FIB.
- No dependencies and `no_std` support. 

`prefix-trie` has the following advantages:
- Faster inserts
  - Their individual inserts definitely scale better. At large scales though, it's likely that you'd want to rebuild the trie and our bulk construction scales similarly to theirs at a constant x2 overhead.
- More mature API
  - They have support for `PrefixSet`, `Entry` and `TrieView`/`TrieMutView` which we haven't yet implemented. Their codebase is very well documented as battle tested.

## `pixos/poptrie`
[pixos/poptrie](https://github.com/pixos/poptrie) is the reference implementation in C for the original Poptrie paper. A thin Rust wrapper was developed around its API for benchmarking purposes.

Compared to it, this crate offers many advantages:
- More performant lookups (at least up to 100k entries)
  - This is despite our crate not yet implementing "Direct Pointing", which is reported to provide a boost to lookup performance in the original paper. It could be due to better cache locality with our very contiguous memory layout compared to their buddy allocator.
- More ergonomic API
  - Our crate provides all the basic `iter` utilities (including a very efficient construction with `FromIterator`), generic prefixes and value types and other quality of life features.
- More stable
  - `pixos/poptrie` eventually crashes when running high scale benchmark loads.
- Better prefix support
  - They apparently don't support prefixes more specific than /24.

The `pixos/poptrie` has the following advantage:
- Faster inserts at very high scale.
  - At 100k entries, their insertion is faster, which is likely due to the way they allocate memory.

## `oxidecomputer/poptrie`
[oxidecomputer/poptrie](https://github.com/oxidecomputer/poptrie) is also a pure Rust, `no_std` implementation of poptrie.

Compared to it, this crate has many advantages:
- Better lookup performance
  - This is likely due to their implementation of leaf construction, which does not make full use of the "leafvec" optimization described in the paper.
- Support for individual inserts
  - Their crate supports only reconstructing the trie, which is a sensible way of implementing simple and efficient MVCC consistency for a FIB.
- Slightly faster construction

`oxidecomputer/poptrie` has the following advantage:
- Support for arbitrarily sized addresses / prefixes
  - Their generic bit extraction function operates over a byte array, which allows them to support a wide variety of addresses / prefixes.
