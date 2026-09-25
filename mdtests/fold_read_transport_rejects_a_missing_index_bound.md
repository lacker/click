# a store with no bound relating it to the range is not framed

The written index `j` lies in the array, but nothing places it below `lo` or
at or above `hi`. The rule does not guess which side it is on.

```c filename=fold_read_transport_rejects_a_missing_index_bound.c
void mark_somewhere(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    v[j] = 1;
}
```

```click
verifying "fold_read_transport_rejects_a_missing_index_bound.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_somewhere(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    requires 0 <= lo;
    requires lo <= hi;
    requires hi <= n;
    requires 0 <= j;
    requires j < n;
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
