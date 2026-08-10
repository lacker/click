# Owned Split Buffer

This project verifies a buffer divided into two independently owned adjacent
partitions by mutable metadata.

```c
struct owned_split_buffer {
    int32 split;
    int32 len;
    int32* data;
};
```

The `owned_split_buffer(owner)` composite resource owns the metadata and the
two sibling ranges `data[0..split]` and `data[split..len]`. It records
`0 <= split <= len` and separation between the metadata and backing storage.

The left and right setters mutate one partition while framing the other.
`owned_split_buffer_move_right` changes only the split metadata and transfers
one element from the right partition to the left partition without changing
the backing memory. The pipeline composes all operations through their verified
contracts and then reads the transferred element through the left partition.

The sidecar mixes concise smart proofs with expanded exact certificates. Read
the small setter/accessor proofs first. Long `step() using`, `transport ...
using`, and explicit rewrite blocks are checked replay artifacts retained for
predictable performance and expansion coverage, not the recommended first
draft of a proof. Restricted `simp() using` arithmetic expands through named
standard theorems rather than retaining a hidden arithmetic search.

The caller supplies the backing storage. Allocation, deallocation, and resizing
are outside this example's scope.
