# a fold reading one cell past its binder is not summarized

`ahead` reads `v[k + 1]`, so its last iteration reads `v[hi]`. The store at
the endpoint writes that cell; the definition is declined and the transport
refused.

```c filename=fold_read_transport_rejects_a_shifted_read.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_rejects_a_shifted_read.c";

function ahead(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k + 1] == 0 { 1 } else { 0 }) })
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 1 <= i;
    requires i < n;
    owns v[0..n];
    ensures ahead(v, 0, i) == old(ahead(v, 0, i));
} by {
    mark entry;
    have ahead(at(entry, v), 0, i) == ahead(at(entry, v), 0, i) by { normalize(); }
    step();
    have ahead(at(entry, v), 0, i) == ahead(v, 0, i) by {
        transport(
            ahead(at(entry, v), 0, i) == ahead(at(entry, v), 0, i),
            ahead(at(entry, v), 0, i) == ahead(v, 0, i)
        ) using {
            ahead(at(entry, v), 0, i) == ahead(at(entry, v), 0, i);
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: fold read frame: `ahead` has no checked read summary: the fold body reads the array at an index other than the fold's own binder
```
