# A guard decided across a sibling write inside one inlined statement

An inlined helper is one statement at the proof frontier: `execute()` runs its
whole body, and every `if` inside it has to be decided from the facts the proof
holds *before* the statement. This fixture is the positive case. `probe` writes
one owned cell and then reads a different owned cell in its guard; both cells
are members of the same validated composition, so the write cannot have changed
the one the guard reads, and the guard keeps the contract's requirement.

Both the integer and the pointer guard are here because they take different
routes through the checker: a wide scalar cell reads back through its load
variable, and a pointer cell reads back as a pointer value.

The negative is
[`guard_after_sibling_write_through_unfold.md`](guard_after_sibling_write_through_unfold.md),
which is this same C with the guard's cell owned through an unfolded resource
arm instead of a contract clause.

```c filename=sibling_write.c
struct pair {
    int32 a;
    int32 b;
};

struct link {
    struct link *next;
    int32 tag;
};

static inline void probe_int(struct pair *x, struct pair *y, int32 *out) {
    y->a = 7;
    if (x->b == 3)
        out[0] = 1;
    else
        out[0] = 2;
}

static inline void probe_ptr(struct link *x, struct link *y, struct link *z, int32 *out) {
    y->tag = 7;
    if (x->next == z)
        out[0] = 1;
    else
        out[0] = 2;
}

void run_int(struct pair *x, struct pair *y, int32 *out) {
    probe_int(x, y, out);
}

void run_ptr(struct link *x, struct link *y, struct link *z, int32 *out) {
    probe_ptr(x, y, z, out);
}
```

```click
verifying "sibling_write.c";

void run_int(struct pair* x, struct pair* y, int32* out) {
    owns x->b;
    owns y->a;
    owns out[0..1];
    requires x->b == 3;
    ensures out[0] == 1;
} by {
    execute();
    simp();
}

void run_ptr(struct link* x, struct link* y, struct link* z, int32* out) {
    owns x->next;
    owns y->tag;
    owns out[0..1];
    requires x->next == z;
    ensures out[0] == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
