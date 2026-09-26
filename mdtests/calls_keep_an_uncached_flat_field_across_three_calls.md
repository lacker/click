# Three calls keep a caller's uncached flat cell

The three-call form of
`call_keeps_an_uncached_flat_field_beside_folded_state.md`. `keep` owns
`b->v` flat and never loads it before its return: at each of the three calls
lending the folded `cells` to `touch`, the cell has no cached value. Each
call's havoc edge records the residual member `b->v` from the caller's
ownership, so an explicit `transport` carries its entry value across all
three calls, one call at a time, and the return reads it.

```c filename=calls_keep_an_uncached_flat_field_across_three_calls.c
struct box {
    int32 v;
};

void touch(int32* flags, int32* data, int32 n) {
    return;
}

int32 keep(int32* flags, int32* data, int32 n, struct box* b) {
    touch(flags, data, n);
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

verifying "calls_keep_an_uncached_flat_field_across_three_calls.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
} by {
    execute();
    simp();
}

int32 keep(int32* flags, int32* data, int32 n, struct box* b) {
    owns cells(flags, data, n);
    owns b->v;
    ensures result == old(b->v);
} by {
    mark m0;
    step();
    mark m1;
    have at(m1, b->v) == old(b->v) by {
        transport(at(m0, b->v) == old(b->v), at(m1, b->v) == old(b->v)) using {
            at(m0, b->v) == old(b->v);
        }
    }
    step();
    mark m2;
    have at(m2, b->v) == old(b->v) by {
        transport(at(m1, b->v) == old(b->v), at(m2, b->v) == old(b->v)) using {
            at(m1, b->v) == old(b->v);
        }
    }
    step();
    have b->v == old(b->v) by {
        transport(at(m2, b->v) == old(b->v), b->v == old(b->v)) using {
            at(m2, b->v) == old(b->v);
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
