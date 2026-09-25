# `simp` composes a pointer-field chain across a call

`first` and `second` point at one arena. `touch(second)` keeps
`second->arena` and `second->arena->data`. Each link of
`first->arena->data == at(m, first->arena->data)` is proved separately:
`first->arena->data == second->arena->data` (both arena pointers are
`arena`), `second->arena->data == at(m, second->arena->data)` (the callee's
frame), and `at(m, second->arena->data) == at(m, first->arena->data)`. The
closing `simp` composes the three.

Its equality-rewrite chain used to keep only the first rewrite that changed
the goal and continue from it; here that was an alias rewrite at the other
snapshot, from which no further link closed, so `simp` reported that
`first->arena` may have changed. Each link now keeps up to four
goal-changing rewrites: the first continues the chain and each other gets a
one-link closing probe, so the order in which candidates were found no
longer decides whether a chain closes.

```c filename=simp_composes_a_pointer_field_chain_across_a_call.c
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
verifying "simp_composes_a_pointer_field_chain_across_a_call.c";

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
pass
```
