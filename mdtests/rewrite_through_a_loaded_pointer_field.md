# Equality reaches a load through a loaded pointer

`o->in->cells[2]` reads memory at an address that is itself read from
memory. The read of `o->in` keeps its own name: only the precondition
`o->in == a` relates it to `a`, and lowering never rewrites through a fact
(`docs/internals/raise-lower-principle.md`). `rewrite(o->in, a)` moves the nested
read to `a->cells[2]`, named as lowering names it, and `normalize()` closes
the resulting reflexive goal. `close()` checks the adjacent cell through the
same relationship.

The per-cell arena pipeline uses this pattern: its contracts are stated
through `region->arena`, and the caller's invariant through `arena`.

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
    owns *o;
    owns *a;
    owns a->cells[0..4];
    requires o->in == a;
    ensures result == 0;
} by {
    have o->in->cells[2] == a->cells[2] by {
        rewrite(o->in, a);
        normalize();
    }
    have o->in->cells[3] == a->cells[3] by {
        close();
    }
}
```

```expect
pass
```
