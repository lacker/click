# Detachable Buffer

This project verifies a fixed-size buffer whose backing-array ownership can be
detached from its metadata owner and later attached again.

```c
struct detachable_buffer {
    int32 len;
    int32* data;
};
```

`attached_buffer(owner)` owns the two metadata fields and the field-dependent
backing range. `detached_buffer(owner)` owns only the metadata fields, while a
separate `detached_backing(data, length)` resource carries the backing range.
Attachedness is a proof state rather than a redundant runtime flag.

The detach operation transforms `attached_buffer(owner)` into
`detached_buffer(owner)` plus `detached_backing(data, length)`. Attach consumes
those two resources and constructs a fresh attached state. The pipeline
initializes an attached buffer, detaches it, changes the first element through
a function that knows nothing about the owner, reattaches it, and calls the
viewed getter through the folded composite resource. Its postconditions also
show that the detached mutation survives reattachment.

The caller supplies the metadata object and backing array. Allocation,
deallocation, resizing, and transferring the backing pointer to a different
metadata owner are outside this example's scope.
