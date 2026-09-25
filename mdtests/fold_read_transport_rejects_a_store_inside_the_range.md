# a store inside the fold's range is not framed

`v[j]` with `lo <= j < hi` is a cell `zeros(v, lo, hi)` reads, and the store
can change its count. The transport is refused.

```c filename=fold_read_transport_rejects_a_store_inside_the_range.c
void mark_inside(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    v[j] = 1;
}
```

```click
verifying "fold_read_transport_rejects_a_store_inside_the_range.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_inside(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    requires 0 <= lo;
    requires lo <= j;
    requires j < hi;
    requires hi <= n;
    owns v[0..n];
    ensures zeros(v, lo, hi) == old(zeros(v, lo, hi));
} by {
    mark entry;
    have zeros(at(entry, v), lo, hi) == zeros(at(entry, v), lo, hi) by { normalize(); }
    step();
    have zeros(at(entry, v), lo, hi) == zeros(v, lo, hi) by {
        transport(
            zeros(at(entry, v), lo, hi) == zeros(at(entry, v), lo, hi),
            zeros(at(entry, v), lo, hi) == zeros(v, lo, hi)
        ) using {
            zeros(at(entry, v), lo, hi) == zeros(at(entry, v), lo, hi);
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
