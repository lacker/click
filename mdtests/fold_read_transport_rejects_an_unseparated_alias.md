# distinct parameter names do not separate two arrays

The store of `fold_read_transport_through_a_separated_alias.md` without the
stated separation. A caller may pass one array as both `a` and `b`, and then
the store writes a cell `zeros(a, 0, n)` reads.

```c filename=fold_read_transport_rejects_an_unseparated_alias.c
void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    b[j] = 1;
}
```

```click
verifying "fold_read_transport_rejects_an_unseparated_alias.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    requires 0 <= j;
    requires j < n;
    owns b[0..n];
    ensures zeros(a, 0, n) == old(zeros(a, 0, n));
} by {
    mark entry;
    have zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n) by { normalize(); }
    step();
    have zeros(at(entry, a), 0, n) == zeros(a, 0, n) by {
        transport(
            zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n),
            zeros(at(entry, a), 0, n) == zeros(a, 0, n)
        ) using {
            zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n);
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: fold read frame: a `store` step between the two `zeros` snapshots was not shown to miss the cells the fold reads
```
