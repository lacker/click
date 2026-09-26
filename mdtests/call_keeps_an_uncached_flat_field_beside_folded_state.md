# A call keeps a caller's flat cell whether or not its value is cached

`keep` owns `b->v` flat beside the folded `cells` it lends to `touch`. The
call rule keeps a cell an owned member of the caller's residual resources
holds (`call_keeps_caller_object_beside_folded_state.md`). Here `give(b)` runs
first and leaves `b->v` uncached: its postcondition relates the value, it
caches nothing, and its havoc drops the entry cell. The havoc edge of `touch`
still records the caller's flat member `b->v`, because the kept ranges are
read from the residual ownership (every owned flat member in a block the
write set may alias, through the per-block owned-memory index), not from the
cells the havoc found cached. So `simp` names `b->v` across `touch` at its
value before the call, and `give`'s postcondition carries it back to entry.

The arena example meets the same shape in `arena_reuse`, where
`middle->arena` is read after `arena_free(middle)` returned the descriptor and
must be related across the following `arena_alloc`.

```c filename=call_keeps_an_uncached_flat_field_beside_folded_state.c
struct box {
    int32 v;
};

void touch(int32* flags, int32* data, int32 n) {
    return;
}

void give(struct box* b) {
    return;
}

int32 keep(int32* flags, int32* data, int32 n, struct box* b) {
    give(b);
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

verifying "call_keeps_an_uncached_flat_field_beside_folded_state.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
} by {
    execute();
    simp();
}

void give(struct box* b) {
    owns b->v;
    ensures b->v == old(b->v);
} by {
    execute();
    simp();
}

int32 keep(int32* flags, int32* data, int32 n, struct box* b) {
    owns cells(flags, data, n);
    owns b->v;
    ensures result == old(b->v);
} by {
    step();
    mark m;
    step();
    have b->v == at(m, b->v) by {
        simp();
    }
    execute();
    simp();
}
```

```expect
pass
```
