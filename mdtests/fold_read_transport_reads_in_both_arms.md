# repeated reads of the fold's cell in both arms are one support

`weighted` reads `v[k]` in its condition and in both arms. Every read is the
array at the fold's own binder, so the support is still `lo <= k < hi`, and
the store at the endpoint misses it.

```c filename=fold_read_transport_reads_in_both_arms.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_reads_in_both_arms.c";

function weighted(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { v[k] } else { v[k] }) })
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures weighted(v, 0, i) == old(weighted(v, 0, i));
} by {
    mark entry;
    have weighted(at(entry, v), 0, i) == weighted(at(entry, v), 0, i) by { normalize(); }
    step();
    have weighted(at(entry, v), 0, i) == weighted(v, 0, i) by {
        transport(
            weighted(at(entry, v), 0, i) == weighted(at(entry, v), 0, i),
            weighted(at(entry, v), 0, i) == weighted(v, 0, i)
        ) using {
            weighted(at(entry, v), 0, i) == weighted(at(entry, v), 0, i);
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
