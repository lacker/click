# a framed fold equality grants no C read

The transport carries `zeros(v, 0, i) == 0` across the endpoint store. That
is a logical equality between two opaque applications: it says nothing about
whether `v[0]` may be read. The function holds no resource for the cells
below `i`, so its C read of `v[0]` is still refused.

```c filename=fold_read_transport_grants_no_c_read.c
int32 set_then_read(int32 *v, int32 i) {
    v[i] = 1;
    return v[0];
}
```

```click
verifying "fold_read_transport_grants_no_c_read.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

int32 set_then_read(int32 *v, int32 i) {
    requires 0 < i;
    requires i < 1000;
    requires zeros(v, 0, i) == 0;
    owns v[i..(i + 1)];
} by {
    mark entry;
    step();
    have zeros(v, 0, i) == 0 by {
        transport(
            at(entry, zeros(v, 0, i)) == 0,
            zeros(v, 0, i) == 0
        ) using {
            at(entry, zeros(v, 0, i)) == 0;
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: missing resource fact `views v[0..1]`
```
