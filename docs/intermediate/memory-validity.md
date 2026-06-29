# Memory Validity

Pointer proofs start with validity. Before Click can prove what a memory access
returns, it must first know that the access is allowed.

For an array parameter:

```c
int32 first(int32 p[]) {
    return p[0];
}
```

the contract needs:

```click
int32 first(int32 p[]) {
    requires valid_range(p[0..1]);
    ensures result == p[0] by auto;
}
```

## Ranges

`valid_range` uses half-open ranges:

```click
requires valid_range(p[0..n]);
```

This covers indices `0` through `n - 1`. For `int32 p[]`, each element is a
four-byte access. For `uint8 p[]`, each element is a one-byte access.

You can also write shifted ranges:

```click
requires valid_range((p + 1)[0..n - 1]);
```

## Index Bounds

A valid range is not enough by itself if the index is symbolic. Click also needs
to know the index is inside the range:

```click
requires 0 <= k;
requires k < n;
requires valid_range(p[0..n]);
ensures result == p[k] by auto;
```

Loops usually need invariants to preserve these bounds at every iteration.

## Old Memory

`old(...)` reads from the function-entry state:

```click
ensures p[0] == old(p[0]) by auto;
```

This is how postconditions talk about preservation or change. The expression
inside `old(...)` still needs to be meaningful in the entry state, so memory
validity requirements still matter.

## Field Validity

The current struct support is intentionally narrow. For the json-c-shaped pilot,
Click accepts:

```click
requires valid_field(obj->ref_count);
mutable obj->ref_count by frame;
```

This is not yet a general struct layout model. It is a focused slice to support
the current example project while the broader memory model is still growing.
