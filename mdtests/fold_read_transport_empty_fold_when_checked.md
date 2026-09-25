# a checked empty fold crosses a store anywhere

`zeros(v, lo, hi)` with `hi <= lo` reads no cell at all: its value is the
initial accumulator. The store to `v[j]` is not placed relative to the range,
and it need not be, because the context proves the range empty.

```c filename=fold_read_transport_empty_fold_when_checked.c
void mark_any(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    v[j] = 1;
}
```

```click
verifying "fold_read_transport_empty_fold_when_checked.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_any(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    requires 0 <= j;
    requires j < n;
    requires hi <= lo;
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
