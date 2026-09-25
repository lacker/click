# a function that reads past its fold range gets no narrowed support

`peek` folds over `lo..hi` but its body also reads `v[hi]`, the very cell the
endpoint store writes. The kernel declines its whole definition rather than
summarize the in-range reads, so the store is not framed and the array
argument keeps its whole-array dependency.

```c filename=fold_read_transport_rejects_a_read_outside_the_range.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_rejects_a_read_outside_the_range.c";

function peek(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { v[hi] } else { 0 }) })
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures peek(v, 0, i) == old(peek(v, 0, i));
} by {
    mark entry;
    have peek(at(entry, v), 0, i) == peek(at(entry, v), 0, i) by { normalize(); }
    step();
    have peek(at(entry, v), 0, i) == peek(v, 0, i) by {
        transport(
            peek(at(entry, v), 0, i) == peek(at(entry, v), 0, i),
            peek(at(entry, v), 0, i) == peek(v, 0, i)
        ) using {
            peek(at(entry, v), 0, i) == peek(at(entry, v), 0, i);
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: fold read frame: `peek` has no checked read summary: the fold body reads the array at an index other than the fold's own binder
```
