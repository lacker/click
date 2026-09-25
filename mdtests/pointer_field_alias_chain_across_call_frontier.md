# A pointer-field equality chain across a call is the frontier

`first` and `second` point at one arena. `touch(second)` keeps
`second->arena` and `second->arena->data`. Every link of
`first->arena->data == at(m, first->arena->data)` is proved separately
below: `first->arena->data == second->arena->data` (both arena pointers are
`arena`), `second->arena->data == at(m, second->arena->data)` (the callee's
frame), and `at(m, second->arena->data) == at(m, first->arena->data)`. The
closing `simp` still fails: its equality-rewrite chain does not compose
pointer-offset equalities between loaded pointer fields across two
snapshots, and it reports that `first->arena` may have changed.

The per-cell arena pipeline needs this chain for every value it carries
across a call through the other region (`first`'s data across
`arena_write(second, ..)`), so this file pins the frontier it stops at.
When `simp` composes the chain this file should pass unchanged.

```c filename=pointer_field_alias_chain_across_call_frontier.c
struct arena {
    int* data;
};

struct region {
    struct arena* arena;
};

void touch(struct region* region) {
}

int caller(struct arena* arena, struct region* first, struct region* second) {
    touch(second);
    return 0;
}
```

```click
verifying "pointer_field_alias_chain_across_call_frontier.c";

void touch(struct region* region) {
    owns object(region);
    owns &region->arena->data;
    requires separate(memory(object(region)), memory(&region->arena->data));
    ensures region->arena == old(region->arena);
    ensures region->arena->data == old(region->arena->data);
} by {
    execute();
    simp();
}

int32 caller(struct arena* arena, struct region* first, struct region* second) {
    owns object(arena);
    owns object(first);
    owns object(second);
    requires first->arena == arena;
    requires second->arena == arena;
    ensures result == 0;
} by {
    mark m;
    step();
    have second->arena == arena by {
        simp();
    }
    have first->arena == arena by {
        simp();
    }
    have first->arena->data == second->arena->data by {
        rewrite(first->arena == arena);
        rewrite(second->arena == arena);
        normalize();
    }
    have second->arena->data == at(m, second->arena->data) by {
        simp();
    }
    have at(m, second->arena->data) == at(m, first->arena->data) by {
        simp();
    }
    have first->arena->data == at(m, first->arena->data) by {
        simp();
    }
    execute();
    simp();
}
```

```expect
fail: `simp` failed for `caller.contract`
```
