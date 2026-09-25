# A borrowed instance named through a field the callee may write

`use` borrows `st: state(..)` for the arena its region points to. The region
descriptor is owned by the folded `r: reg(region)`, so `use` may write
`region->arena`, and a borrowed instance is re-read at the call's return:
`state(region->arena)` would then name whatever `region->arena` holds after
the call, before the caller could apply `ensures region->arena ==
old(region->arena)`, and the caller's `state(arena)` would not match it. The
contract instead names the instance by the entry value,
`state(old(region->arena))`, which is the arena the caller lent.

Reading `old(region->arena)` at the callee's entry used to fail: an entry
argument was read in the bare entry state, while the clause itself was read
in the frame that adds the folded `reg` instance's cells as read authority.
Both read the same snapshot, so the entry argument now reads through the
same frame. Two calls in a row then bind the caller's `state(arena)` each
time.

```c filename=borrowed_instance_argument_reads_old_field.c
struct arena {
    int capacity;
};

struct region {
    struct arena* arena;
    int start;
};

void use(struct region* region) {
}

int caller(struct arena* arena, struct region* a) {
    use(a);
    use(a);
    return 0;
}
```

```click
resource state(arena: struct arena*) {
    field live: int32;
    owns object(arena);
}

resource reg(region: struct region*) {
    field start: int32;
    owns object(region);
    fact region->start == start;
}

verifying "borrowed_instance_argument_reads_old_field.c";

void use(struct region* region) {
    owns r: reg(region);
    owns st: state(old(region->arena));
    ensures region->arena == old(region->arena);
} by {
    let { start: s } = unfold(r);
    execute();
    let r = fold(reg(region), { start: s });
    simp();
}

int32 caller(struct arena* arena, struct region* a) {
    owns st: state(arena);
    owns object(a);
    requires a->arena == arena;
    ensures result == 0;
} by {
    let r = fold(reg(a), { start: a->start });
    step(use(a), { r: r, st: st });
    have a->arena == arena by {
        simp();
    }
    step(use(a), { r: r, st: st });
    unfold(r);
    execute();
    simp();
}
```

```expect
pass
```
