# Benchmarks
This document describes the benchmarking approach used to evaluate the performance of `nicolaskagami/poptrie` against other similar libraries. 


## Setup
A common trait was implemented for each contender and they were benchmarked using `criterion` under the exact same input and conditions. All candidates were built with `-C target-cpu=native`. Benchmarks were run on an AMD Ryzen 9 7900 (12-core, x86_64), Linux kernel 6.18, rustc 1.93.1.

## Input
A list of random Ipv4 prefixes is generated for each benchmark run based on realistic distributions from https://bgp.potaroo.net/as2.0/bgp-active.html. For insertion and construction, `criterion` assesses the time each candidate takes to completely incorporate these prefixes. For lookup, a separate list of lookups is generated and `criterion` assesses the time each candidate takes to perform an LPM lookup for all entries. Both of these lists varied in size from 1k to 100k entries.


## Candidates
| Candidate | Version |
|---|---|
| **nicolaskagami/poptrie** (this crate) | [dfe2ed77fe930baef5e07e2c8ca5c224e52c519f](https://github.com/nicolaskagami/poptrie/tree/dfe2ed77fe930baef5e07e2c8ca5c224e52c519f) |
| [pixos/poptrie](https://github.com/pixos/poptrie) (with Rust bindings) |  [845c3b4663ea58395eb11a6c448230284ebd8c90](https://github.com/pixos/poptrie/tree/845c3b4663ea58395eb11a6c448230284ebd8c90)|
| [tiborschneider/prefix-trie](https://github.com/tiborschneider/prefix-trie) | [ce1603e2b6573be61699838f95b5d396b89ae83f](https://github.com/tiborschneider/prefix-trie/tree/ce1603e2b6573be61699838f95b5d396b89ae83f)  |
| [oxidecomputer/poptrie](https://github.com/oxidecomputer/poptrie) | [5bf62f6b889c61e0608d8463ed11da28e130cb34](https://github.com/oxidecomputer/poptrie/tree/5bf62f6b889c61e0608d8463ed11da28e130cb34) |


## Lookup
| Implementation | 1k prefixes | 10k prefixes | 100k prefixes |
|---|---|---|---|
| **nicolaskagami/poptrie** (this crate) | 461.89 Mlookups/s | 324.56 Mlookups/s | 175.44 Mlookups/s |
| [pixos/poptrie](https://github.com/pixos/poptrie) (with Rust bindings) | 400.93 Mlookups/s | 332.54 Mlookups/s | 166.75 Mlookups/s |
| [tiborschneider/prefix-trie](https://github.com/tiborschneider/prefix-trie) | 300.95 Mlookups/s | 296.49 Mlookups/s | 110.92 Mlookups/s |
| [oxidecomputer/poptrie](https://github.com/oxidecomputer/poptrie) | 309.60 Mlookups/s | 212.84 Mlookups/s | 95.01 Mlookups/s |

## Insert
| Implementation | 1k prefixes | 10k prefixes | 100k prefixes |
|---|---|---|---|
| [tiborschneider/prefix-trie](https://github.com/tiborschneider/prefix-trie) | 22.6 Minserts/s | 14.0 Minserts/s | 9.21 Minserts/s |
| **nicolaskagami/poptrie** (this crate) | 790 Kinserts/s | 159 Kinserts/s | 24.4 Kinserts/s |
| [pixos/poptrie](https://github.com/pixos/poptrie) (with Rust bindings) | 98.4 Kinserts/s | 112 Kinserts/s | 126 Kinserts/s |

> [oxidecomputer/poptrie](https://github.com/oxidecomputer/poptrie) does not provide an API for individual inserts.

## Construction
| Implementation | 1k prefixes | 10k prefixes | 100k prefixes |
|---|---|---|---|
| [tiborschneider/prefix-trie](https://github.com/tiborschneider/prefix-trie) | 26.4 Minserts/s | 14.4 Minserts/s | 9.30 Minserts/s |
| **nicolaskagami/poptrie** (this crate) | 10.7 Minserts/s | 5.84 Minserts/s | 5.31 Minserts/s |
| [oxidecomputer/poptrie](https://github.com/oxidecomputer/poptrie) | 5.28 Minserts/s | 4.82 Minserts/s | 4.71 Minserts/s |

> [pixos/poptrie](https://github.com/pixos/poptrie) does not provide an API for bulk construction.
