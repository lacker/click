# Consecutive calls do not keep an uncached cell the caller only views

The negative of `calls_keep_an_uncached_flat_field_across_three_calls.md`:
`keep` holds `b->v` only as a view. A view's owner may be anywhere, including
inside the `cells` the caller lends, so each call may write the cell. The kept
ranges a call records come from what the caller *owns* outside the transfer,
and a view is not ownership, so no edge records `b->v` and the `transport`
across the calls finds no frame evidence
(`call_havocs_cell_the_caller_only_views.md` pins the one-call, cached form).

```c filename=calls_havoc_an_uncached_field_the_caller_only_views.c
struct box {
    int32 v;
};

void touch(int32* flags, int32* data, int32 n) {
    return;
}

int32 keep(int32* flags, int32* data, int32 n, struct box* b) {
    touch(flags, data, n);
    touch(flags, data, n);
    return b->v;
}
```

```click
resource cells(flags: int32*, data: int32*, n: int32) {
    owns flags[0..n];
    forall (k: int32) where 0 <= k and k < n {
        if flags[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "calls_havoc_an_uncached_field_the_caller_only_views.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
} by {
    execute();
    simp();
}

int32 keep(int32* flags, int32* data, int32 n, struct box* b) {
    owns cells(flags, data, n);
    views b->v;
    ensures result == old(b->v);
} by {
    mark m0;
    step();
    step();
    have b->v == old(b->v) by {
        transport(at(m0, b->v) == old(b->v), b->v == old(b->v)) using {
            at(m0, b->v) == old(b->v);
        }
    }
    execute();
    simp();
}
```

```expect
fail: `transport using` found no frame evidence
```
