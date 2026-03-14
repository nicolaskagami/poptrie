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

Our main goal is to provide a reliable and efficient solution to LPM lookups in Rust.
This means not using `unsafe`, having few dependencies (or none, so far), and being `no_std` so that it can be used in a wide range of environments.
`Poptrie` currently require `alloc` but we could eventually develop our own memory management given a chunk of memory. 
It wouldn't be that far fetched as it's already very opinionated about how things are stored.

The poptrie paper provides many optimizations that are useful for performance. We implemented most of them and added a few of our own. The focus lies mostly on cache locality and reducing lookup complexity. We'll make tradeoffs that benefit lookup performance over everything, except for correctness and safety.
After those two, we'll try to make the API ergonomic, like Rust developers can expect from a map-like collection.

## Poptrie Implementation

The poptrie algorithm uses a trie data structure with popcount-based indexing. This means that it keeps bitmaps for indexing entries on a contiguous space. For example, if we have a bitmap of 4 bits with entries 0 and 2 it would look like this: `0101`. The offset for an entry is determined by counting the number of 1s to the right of it (or left, as long as you're consistent). Thus, `offset(0) = 0` and `offset(3) = 1`. During a longest-prefix-match lookup, these bitmaps are used to navigate the internal nodes according to the address that is being looked up. The address is consumed in chunks (which I call "strides") of a fixed size, conventionally determined to be as big as it can be efficient to popcount the bitmap.
This allows the poptrie to compress ranges and efficiently navigate them.
```
offset = if id == 0 { 0 } else { (bitmap << (BITMAP_SIZE - id)).count_ones() };
```

### Internal Structure
The poptrie is made of nodes, each of which contains a bitmap for its children nodes and another for its leaves, which point to the actual values. Given a full-sized stride, we first check if an entry exists in the node bitmap, otherwise we check the leaf bitmap. This is very important to guarantee correctness for more specific subranges that cross the stride boundary (*). Besides these bitmaps, each node needs to store the offset (or, a "pointer") to the beginning of the contiguous section that contains the bitmap entries.

While in the original implementation these nodes are stored using the buddy allocator, my implementation stores nodes, leaves and values in vectors. This is advantageous in that it is practical and minimizes fragmentation, but it also means inserts are more costly and we don't have guarantees of locality between the vectors. Within the vectors, nodes and leaves are stored in a heap-like order but compacted, meaning they are organized by depth and then by their stride identifier. Having strong guarantees about this ordering allows us to simplify trie manipulation and poises us to make other optimizations in the future.

> \* By construction we guarantee that prefixes that specify the entire local stride will always be found in the node bitmap, never the leaf bitmap. This is required for all but the last stride, but, by always enforcing it, we can guarantee that a leaf bitmap needs to encode one less bit, which can halve its size.

### Leafvec Optimization
The poptrie paper presents the "leafvec" optimization as a way to reduce space usage, but its explanation can be a little confusing. I believe the confusion stems from two possible interpretations of how cross-level subranges should be treated. This is the problem where we traverse a node bitmap but the address matches no prefixes more specific than it. My first interpretation was that "one should remember valid less specific prefixes", but this is not correct. Actually, these "default" values are supposed to be pushed out to every node and be reflected in their leaves. This means that every nodes' leaves need to encode the entirety of their representation space, filling out the blanks with the default. Semantically, the leaves actually encode ranges of representation rather than prefix entries, which has many implications:
- A prefix entry `(P -> V)` can have its range of representation segmented by more specific subranges, mapping to multiple leaves.
- Unlike the node bitmap, where each node is mapped to a specific bit, we cannot rely on the leaves to retrieve prefix entries, since they are a sort of palimpsest where any range overlap is overwritten. We therefore need an auxiliary structure to keep track of these entries.
- The most specific associated value before this node needs to be pushed as the default value, unless supplanted by a local `/0` prefix. In both cases, I found it beneficial to always have a default leaf for a node.
- The way ranges are encoded and read is also different from the node bitmap. Here again there can be confusion regarding two possible interpretations of how to extract these bits, which is further detailed on the Bit Extraction section.

The leafvec optimization is defined as simply having a distinct bitmap for internal nodes and leaf nodes, which allows this contiguity in the leaf ranges.
These ranges are efficiently mapped by a little trick that allows some contiguity between leaf values as long as the partial strides maintain bit-position.

Let's say you have an address of 10 bits, a stride length of 4 bits and you want to encode the `00001/5` prefix. This matches any address like `00001XXXXX` (where `X` is "don't care"). When installing this prefix, we go by the strides of 4 bits. The first stride is `0000`, which means we traverse into the node with that id. The second stride is supposed to extract an identifier of 4 bits but there is only 1 significant bit left. This could be interpreted as `XXX1` or `1XXX`, which wasn't a problem when we had full-length strides. If we wanted to reliably store every prefix entry in the leaves we'd have to go with `XXX1` (and use `PrefixId`) but using `1XXX` (actually coded as `1000`) allows a slightly modified popcount to address contiguous ranges effectively:

```
offset = bitmap << (BITMAP_SIZE - 1 - id)).count_ones() - 1
```

The difference is that we include the entry in the count and subtract one. It's easy to see that:
- Any id would map to the "default" leaf at bit position 0, except if there is another entry between 0 and that id.
- If we insert a leaf for `1000`, every `1XXX` will prefer that one and every `0XXX` would prefer the default one.

```text
     15                                                0
     |                                                 |
 MSB |---------------------bitmap----------------------| LSB
     [=======1XXX range=======][=======0XXX range======]
                              ^                        ^
                              1000 entry               0000 entry (default)
```

### Bit Extraction
There are three situations when extracting bits from a key.

- A) Normal full-stride extraction:
```text
 MSB |------------------------key-------------------------| LSB
     |------ offset ------|----- len ----|---remaining----|
                           ^^^^^^^^^^^^^^
                           extracted bits
```
- B) Partial stride extraction that preserves bit position:
```text
 MSB |------------------------key-------------------------| LSB
     |---------------- offset -----------------|----- len ----|
                                               |^^^^^^^^^^0000|
                                                extracted bits
```
- C) Partial stride extraction that preserves magnitude:
``` text
 MSB |------------------------key-------------------------| LSB
     |---------------- offset -----------------|----- len ----|
                                           |0000^^^^^^^^^^|
                                            extracted bits
```

'A' is used exclusively to traverse into internal nodes. 'B' is what we need to use for the consulting the leaves. 'C' is what we would use in the `mask/len` prefix notation and I use it to store the prefix entries (`PrefixId`).


### Prefix Id
`PrefixId` uses a neat trick to uniquely encode any partial prefix, by which I mean the final part of a prefix after consuming as many full strides as possible. This means that the maximum prefix length is `STRIDE - 1`. We could simply store a `(mask, length)` tuple, but `PrefixId` can store this information in `STRIDE` bits.
The inspiration came from how traverse between parent / children in a heap:
```text
| prefix_id | prefix/len |
|-----------|------------|
| 0         | 0/0        |
| 1         | 0/1        |
| 2         | 1/1        |
| 3         | 0/2        |
| 4         | 1/2        |
| 5         | 2/2        | 
| 6         | 3/2        |
```
Defined as: `(1 << len) - 1 + prefix`

Besides being more compact, `PrefixId` allows for easily calculating the "parent" `PrefixId` by simply doing `(p - 1) >> 1`.

### Leaf Construction
When constructing the leaves, we iterate over the `PrefixId` in order. We begin by establishing a default given by its parent node or by a local `/0` prefix.
Then, for each prefix in the tree:
- We check the value that is currently assigned to the position.
- We insert the leaf on its position.
- We insert a terminating leaf where its range would finish if:
  - There isn't already a leaf at that position
  - It is not beyond our representation.

Since `PrefixId` starts with the smallest prefix lengths, the terminator should always have the value that existed initially.

```text
| prefix_id | prefix/len | base | cover | next     |
|-----------|------------|------|-------|----------|
| 0         | 0/0        | 0    | 64    | 64 (out) |
| 1         | 0/1        | 0    | 32    | 32       |
| 2         | 1/1        | 32   | 32    | 64 (out) |
| 3         | 0/2        | 0    | 16    | 16       |
| 4         | 1/2        | 16   | 16    | 32       |
| 5         | 2/2        | 32   | 16    | 48       |
| 6         | 3/2        | 48   | 16    | 64 (out) |
```

Start with `0/0 -> A`, or the default value:
```
       0                              32                             63
       [============================= A ==============================]
```
After inserting `0/1 -> B`, terminating at `1/1` restores `A`:
```
       [============= B =============][============= A =============]
       ^base                          ^term
```
After inserting `0/2 -> C`, terminating at slot `2/2` restores `B`:
```
       [===== C ======][===== B =====][============= A =============]
       ^base           ^term
```

### Longer Strides
Longer strides may provide many benefits to the efficiency of the poptrie algorithm, but these are limited by hardware support.
The scalar `POPCNT` instruction is ubiquitous in modern `x86_64`, the maximum size of which is 64 bits. This is what defines our default stride length of 6 bits, which is the most we can encode in a 64 bit bitmap (2^6 = 64). With the advent of AVX-512, some CPUs have access to vectorized versions of `POPCNT` that operate on 256 or 512 bit vectors, but support is not widespread. One obviously attractive stride length is 8 bits, which would allow for byte-aligned bit extraction (without shifts). My first experiments with this did not provide a comparative gain in performance. Unfortunately larger bitmaps are less efficient to mask before popcounting.

## Generics

The latest `Poptrie` struct is generic over `P:Prefix` and `V`. Values of type `V` are stored in the trie for retrieval and have no explicit constraints (though it needs to be `Sized`).
The `Prefix` trait is an abstraction over address and prefix length, where `Address` is fixed-width and has some shift / rotate constraints that allow efficient bit extraction.
It should be possible to have fewer constraints on `Address` without sacrificing performance but this is not a priority.
Earlier versions (`0.1.*`) were generic over `Address` instead of `Prefix`, but this changed to allow for iterators to return the original `Prefix` instances and to improve `insert` ergonomics.


## Future Improvements
- **Direct Pointing**: This is a very simple tradeoff described in the poptrie paper. A certain number of bits from the address is reserved to be directly mapped into an array, which is basically the uncompressed version of the bitmap strategy (i.e. no bitmap). For example, the paper suggests using 16 bits, which means allocating an array of 2^16 slots to point directly to the next internal node, no popcount necessary. It's much less work for those first 16 bits, which should often be relevant in realistic IPv4 prefixes, but compensates by having a larger memory footprint.
- **Bitmaps that are generic over stride length**: I've already implemented a couple of versions of this. As mentioned above, if I can find an efficient way of masking 256 bits then the lookups would likely be very performant with AVX-512's vectorized `POPCOUNT` and byte-aligned stride. A version with `[u64;4]` was the most performant so far, but still less so thant the current 6-bit stride. I experimented with decreasing the alignment as well (using smaller native integers in the array) in order to eventually decrease the node struct size but this had a negative effect on performance (apparently this matters to the compiler).
- **Relative offset**: This is the most exciting. Instead of storing absolute offsets in nodes, we would store relative offset from the parent. This would cost 1 or 2 extra aditions per stride in the lookup but could reduce memory usage significantly. For example, currently we use `u32` offsets and `u64` bitmaps, which totals `3*u64` per node. This would allow the offset to be a `u16` (the parent would be at most `2^(2*STRIDE)` from its child). Together with the trick to use half representation on leaf bitmaps, we could reduce to `(u64, u32, u16, u16)`, reducing the memory footprint by 33%. It would be nice to see how performance improves, since it's mostly bound by cache locality.
