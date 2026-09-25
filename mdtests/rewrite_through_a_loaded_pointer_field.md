# `rewrite` reaches a load through a loaded pointer

`o->in->cells[2]` reads memory at an address that is itself read from
memory: the kernel names each read by a load variable, and the variable for
`o->in->cells` hides `o->in` inside its registered address. `rewrite(o->in
== a)` used to rewrite only the outermost address and reported that the
equality does not occur. It now rewrites through each registered address a
scaled index names, so the goal becomes `a->cells[2] == a->cells[2]`, which
`normalize()` closes.

`simp` selects the same rewrite: the atoms a goal names now include those of
its loads' addresses, a bounded number of levels deep, and pointer
equalities between scaled offsets are rewrite candidates. The per-cell arena
pipeline needs both: every contract of `arena_free`, `arena_write`, and
`arena_read` is stated through `region->arena`, and the caller's invariant
through `arena`.

```c filename=rewrite_through_a_loaded_pointer_field.c
struct inner {
    int* cells;
};

struct outer {
    struct inner* in;
};

int same(struct outer* o, struct inner* a) {
    return 0;
}
```

```click
verifying "rewrite_through_a_loaded_pointer_field.c";

int32 same(struct outer* o, struct inner* a) {
    owns object(o);
    owns object(a);
    owns a->cells[0..4];
    requires o->in == a;
    ensures result == 0;
} by {
    have o->in->cells[2] == a->cells[2] by {
        rewrite(o->in == a);
        normalize();
    }
    have o->in->cells[3] == a->cells[3] by {
        simp();
    }
    execute();
    simp();
}
```

```expect
pass
```
