# Input Cursor

This project verifies independently mutable cursors over shared read-only input.
It exercises nested composite resources and mixed access modes without adding
allocation or byte-conversion concerns.

```c
struct input_cursor {
    int32 pos;
    int32 len;
    int32* data;
};
```

`readable_input(data, len)` packages a view of the backing array.
`input_cursor(owner)` owns the cursor metadata but contains only a view of that
input resource. Consequently, multiple cursor resources can share the same
`readable_input` while advancing their positions independently.

The verified operations cover initialization, remaining-length inspection,
peeking, consuming one element, and cloning a cursor. Peeking and taking use an
explicit two-step observation chain: first expose the cursor's direct children,
then observe `readable_input` to obtain the backing-memory view. Cloning views
the source cursor while producing independently owned target metadata.

`input_cursor_shared_pipeline` initializes two cursors over the same input,
advances only the left cursor, and proves that the right cursor still reads the
original first element through verified function contracts. Its mutable
footprint contains only the two cursor structs; the shared input remains viewed.

The caller supplies both cursor structs and the backing array. Allocation,
deallocation, and ownership of the backing array are outside this example's
scope.
