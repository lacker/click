# Memory loadability

Pointer proofs start with loadability. Before Click can prove what a memory access
returns, it must know that the access is in bounds. For external memory, Click
also needs permission to access the range; see
[Resources and memory permissions](resources.md).

For an array parameter:

<!-- verified-example: mdtests/pointer_range.md -->
```c
int32 first(int32 p[]) {
    return p[0];
}
```

the contract needs:

<!-- verified-example: mdtests/pointer_range.md -->
```click
int32 first(int32 p[]) {
    views p[0..1];
    ensures result == p[0] by auto;
}
```

Viewed and owned memory resources imply loadability for the range they cover. Use
`loadable(...)` when you need memory-loadability information without granting
access permission, or when the proof needs a larger range than any single
access resource provides.

`loadable(segment)` is the proposition form of the same memory-loadability fact.
It is useful inside predicate-like positions, especially composite resource
`fact` clauses:

<!-- verified-example: mdtests/pointer_range.md -->
```click
fact loadable(data[0..cap]);
```

## Ranges

`loadable` uses half-open ranges:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires loadable(p[0..n]);
```

This covers indices `0` through `n - 1`. For `int32 p[]`, each element is a
four-byte access. For `uint8 p[]`, each element is a one-byte access.

You can also write shifted ranges:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires loadable((p + 1)[0..n - 1]);
```

## Index bounds

A loadable range is not enough by itself if the index is symbolic. Click also needs
to know the index is inside the range:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires 0 <= k;
requires k < n;
requires loadable(p[0..n]);
views p[0..n];
ensures result == p[k] by auto;
```

Loops usually need invariants to preserve these bounds at every iteration.

## Old memory

`old(...)` reads from the function-entry state:

<!-- verified-example: mdtests/pointer_range.md -->
```click
ensures p[0] == old(p[0]) by auto;
```

This is how postconditions talk about preservation or change. The expression
inside `old(...)` still needs to be meaningful in the entry state, so memory
loadability and permission requirements still matter.

## Field resources

For struct fields, prefer field resources:

<!-- verified-example: mdtests/pointer_range.md -->
```click
views obj->ref_count;
consumes obj->data;
```

Those resources imply loadability for the covered fields. A resource addressed
*through* a field reads that field to name itself, so the contract needs the link
cell too: `views node->left->augmented` is only meaningful next to a resource
covering `node->left`, such as `views node->left` or a composite holding it, and
a `requires node->left != 0` guarding the link. A contract that names a segment
through a cell it does not hold is refused where it is prepared.

Explicit ranges remain useful when a proof needs a broader footprint than one
field:

<!-- verified-example: mdtests/pointer_range.md -->
```click
consumes obj[0..3];
```
