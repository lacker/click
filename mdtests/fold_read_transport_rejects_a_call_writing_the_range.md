# a call whose write set covers the fold's range is not framed

`fill` owns `v[0..n]`, so the call may write every cell `zeros(v, 0, i)`
reads, and it does write `v[0]`. The transport is refused.

```c filename=fold_read_transport_rejects_a_call_writing_the_range.c
void fill(int32 *v, int32 n) {
    v[0] = 1;
}

void caller(int32 *v, int32 i, int32 n) {
    fill(v, n);
}
```

```click
verifying "fold_read_transport_rejects_a_call_writing_the_range.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void fill(int32 *v, int32 n) {
    requires 0 < n;
    owns v[0..n];
} by {
    execute();
    simp();
}

void caller(int32 *v, int32 i, int32 n) {
    requires 0 < i;
    requires i < n;
    owns v[0..n];
    ensures zeros(v, 0, i) == old(zeros(v, 0, i));
} by {
    mark entry;
    have zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i) by { normalize(); }
    step();
    have zeros(at(entry, v), 0, i) == zeros(v, 0, i) by {
        transport(
            zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i),
            zeros(at(entry, v), 0, i) == zeros(v, 0, i)
        ) using {
            zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i);
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: fold read frame: a `call` step between the two `zeros` snapshots was not shown to miss the cells the fold reads
```
