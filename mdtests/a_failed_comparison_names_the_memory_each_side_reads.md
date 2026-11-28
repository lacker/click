# a failed comparison names the memory each side reads

`r` holds `a[m]` as it was before the store to `a[i]`; the postcondition reads
`a[m]` after it. Both sides of `result == a[m]` are spelled in the outcome
state, so the spellings alone would say they "both read the outcome state",
which says nothing about why they differ. The two reads are of one address in
two memories, and the refusal names each memory by the point its read is
recorded at: `result` is the read made at function entry, `a[m]` the read at
the return. The resource tracker then names the store in between.

The C returns 7 when `i` and `m` are the same index, so the refusal is
genuine.

```c filename=a_failed_comparison_names_the_memory_each_side_reads.c
int32 stale_read(int32* a, int32 i, int32 m) {
    int32 r;
    r = a[m];
    a[i] = 7;
    return r;
}
```

```click
verifying "a_failed_comparison_names_the_memory_each_side_reads.c";

int32 stale_read(int32* a, int32 i, int32 m) {
    owns a[0..8];
    requires 0 <= i;
    requires i < 8;
    requires 0 <= m;
    requires m < 8;
    ensures result == a[m];
}
```

```expect
fail: unclosed goal: result == a[m]; the two sides read the same address in different memory states (`result` reads the function-entry memory; `a[m]` reads the memory recorded at `statement(3).exit`); `a[m]` may have changed since function entry: the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`.
```
