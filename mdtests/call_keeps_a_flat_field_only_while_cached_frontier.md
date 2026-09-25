# A call keeps a caller's flat cell only while its value is cached (frontier)

`keep` owns `b->v` flat beside the folded `cells` it lends to `touch`. The
call rule keeps a cell an owned member of the caller's residual resources
holds (`call_keeps_caller_object_beside_folded_state.md`), but it records a
flat residual member on the call's havoc edge only when the havoc dropped a
cached value for it. Here `give(b)` runs first and leaves `b->v` uncached (its
postcondition relates the value; it caches nothing), so the edge of `touch`
records no kept range for `b->v`, and neither `simp` nor an explicit
`transport` can carry `b->v` across `touch`, although the callee cannot own
it. Without the earlier call the same frame verifies.

The arena example meets this in `arena_reuse`: `middle->arena`, read after
`arena_free(middle)` returned the descriptor, is not related across the
following `arena_alloc`, so the driver keeps the arena pointer in a local and
its contract names the state it returns through `old(middle->arena)`.
Recording every flat residual member of the write set's blocks on each edge
would close this, at the cost of making every call linear in the caller's
residual members (`a_call_kept_cell_is_placed_without_visiting_unrelated_residual_members`
pins it constant).

```c filename=call_keeps_a_flat_field_only_while_cached_frontier.c
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

verifying "call_keeps_a_flat_field_only_while_cached_frontier.c";

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
fail: `simp` failed
```
