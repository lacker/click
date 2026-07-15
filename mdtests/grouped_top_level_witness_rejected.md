# Grouped existential reasoning is scoped with have

A witness for one postcondition cannot be applied to every goal in a grouped
proof. Establish the existential in a scoped `have` instead.

```c filename=grouped_witness.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "grouped_witness.c";

int32 identity(int32 x) {
    ensures exists (int32 k) { k == result };
} by {
    execute_rest();
    witness(k = result);
    simp();
}
```

```expect
fail: top-level `witness` is not available in a grouped proof
```
