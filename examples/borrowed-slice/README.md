# Borrowed Slice

This project verifies a buffer that temporarily lends ownership of one
symbolic middle slice while retaining its metadata and the two disjoint outer
ranges.

```c
struct borrowed_slice_buffer {
    int32 len;
    int32* data;
};
```

`owned_borrowable_buffer(owner, data, length)` owns the complete backing array
and records its identity explicitly. Borrowing transforms it into
`buffer_without_slice(owner, data, length, start, end)`, which owns the
metadata, prefix, and suffix, plus `owned_slice(data, start, end)`, which owns
the middle range. Returning the slice recombines those resources into the full
buffer.

The pipeline initializes a buffer, lends a nonempty symbolic slice, mutates its
first element through an owner-independent helper, returns the slice, and calls
the ordinary viewed getter after reconstruction. Its postconditions show that
the slice mutation survives the split and rejoin.

The caller supplies the metadata object and backing array. Allocation,
deallocation, overlapping loans, and multiple simultaneous slices are outside
this example's scope.
