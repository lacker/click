# a store below a nonzero lower endpoint misses the fold

`zeros(v, lo, hi)` reads the cells `lo <= k < hi`. The store writes `v[j]`,
and `j < lo` places its four bytes below the first cell the fold reads. The
bound is an exact fact of the context; the frame rule looks it up and does
not search for it.

```c filename=fold_read_transport_below_a_nonzero_start.c
void mark_below(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    v[j] = 1;
}
```

```click
verifying "fold_read_transport_below_a_nonzero_start.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_below(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    requires 0 <= j;
    requires j < lo;
    requires lo <= hi;
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
pass
```
