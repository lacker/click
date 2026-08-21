# Memory loadability

Pointer proofs start with loadability. Before Click can prove what a memory access
returns, it must know that the access is in bounds. For external memory, Click
also needs permission to access the range; see [Permissions](permissions.md).

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

Those resources imply loadability for the covered fields. Explicit ranges remain
useful when a proof needs a broader footprint than one field:

<!-- verified-example: mdtests/pointer_range.md -->
```click
consumes obj[0..3];
```
