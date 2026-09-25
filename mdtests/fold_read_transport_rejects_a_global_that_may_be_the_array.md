# a store to a global is not framed away from an array argument

`caller` passes the global `g` as `v`, and then `g[0] = 1` writes the first
cell `zeros(v, 0, n)` reads. The global's block and the parameter's are two
spellings, not two proven objects, so the fold application is not framed
across the store: carrying `zeros(v, 0, n) == 1` past it would let `caller`
hold both `zeros(g, 0, 4) == 1` and a count that the store changed.

```c filename=fold_read_transport_rejects_a_global_that_may_be_the_array.c
int32 g[4];

void mark_global(int32 v[], int32 n) {
    g[0] = 1;
}
```

```click
verifying "fold_read_transport_rejects_a_global_that_may_be_the_array.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_global(int32 v[], int32 n) {
    requires 0 < n;
    requires n <= 4;
    owns g[0..1];
    ensures zeros(v, 0, n) == old(zeros(v, 0, n));
} by {
    mark entry;
    have zeros(at(entry, v), 0, n) == zeros(at(entry, v), 0, n) by { normalize(); }
    step();
    have zeros(at(entry, v), 0, n) == zeros(v, 0, n) by {
        transport(
            zeros(at(entry, v), 0, n) == zeros(at(entry, v), 0, n),
            zeros(at(entry, v), 0, n) == zeros(v, 0, n)
        ) using {
            zeros(at(entry, v), 0, n) == zeros(at(entry, v), 0, n);
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
