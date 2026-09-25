# passing the array to a helper declines the summary

`through` passes `v` to `cell`, which the summary checker does not enter. The
whole definition is declined, whatever `cell` reads.

```c filename=fold_read_transport_rejects_an_opaque_helper.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_rejects_an_opaque_helper.c";

function cell(v: int32[], k: int32) -> Integer {
    to_integer(v[k])
}

function through(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + cell(v, k) })
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures through(v, 0, i) == old(through(v, 0, i));
} by {
    mark entry;
    have through(at(entry, v), 0, i) == through(at(entry, v), 0, i) by { normalize(); }
    step();
    have through(at(entry, v), 0, i) == through(v, 0, i) by {
        transport(
            through(at(entry, v), 0, i) == through(at(entry, v), 0, i),
            through(at(entry, v), 0, i) == through(v, 0, i)
        ) using {
            through(at(entry, v), 0, i) == through(at(entry, v), 0, i);
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: fold read frame: `through` has no checked read summary: the fold body uses a construct outside the checked subset (a function call)
```
