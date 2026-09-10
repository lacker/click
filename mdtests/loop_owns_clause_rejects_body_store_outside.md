# A loop body store outside the loop's owned memory is rejected

The function owns `q[0..1]`, but the loop declares only `owns p[0..n]`, so the
body views `q` rather than owning it. The store `q[0] = i` has no owned range
covering it and is rejected at the store, not framed away by the loop
footprint.

```c filename=loop_owns_clause_rejects_body_store_outside.c
void loop_owns_clause_rejects_body_store_outside(int32 p[], int32 q[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        q[0] = i;
        i = i + 1;
    }
}
```

```click
verifying "loop_owns_clause_rejects_body_store_outside.c";

void loop_owns_clause_rejects_body_store_outside(int32 p[], int32 q[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    requires loadable(q[0..1]);
    owns p[0..n];
    owns q[0..1];
    requires separate(memory(p[0..n]), memory(q[0..1]));
} by {
    step();
    step();
    loop {
        owns p[0..n];
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    simp();
}
```

```expect
fail: missing resource fact
```
