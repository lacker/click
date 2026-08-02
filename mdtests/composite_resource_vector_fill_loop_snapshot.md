# field-dependent vector storage across loop snapshots

This checks that an owned composite resource whose backing range depends on
owner fields can be used directly through an abstract loop iteration. The loop
mutates only the backing array, so the separate owner metadata and its dependent
backing-range identity remain stable.

```c filename=composite_resource_vector_fill_loop_snapshot.c
struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 composite_resource_vector_fill_loop_snapshot(
    struct vector* owner,
    int32 value
) {
    int32 i;
    i = 0;
    while (i < owner->len) {
        owner->data[i] = value;
        i = i + 1;
    }
    return owner->len;
}
```

```click
resource vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(owner[0..4]), memory(owner->data[0..owner->cap]));
}

verifying "composite_resource_vector_fill_loop_snapshot.c";

int32 composite_resource_vector_fill_loop_snapshot(
    struct vector* owner,
    int32 value
) {
    owns vector(owner);
    mutable owner->data[0..owner->len];

    for loop(0) as fill_cells {
        invariant i >= 0 and i <= owner->len;
        invariant forall (k: int32) {
            0 <= k and k < i implies owner->data[k] == value
        };
        mutable owner->data[0..owner->len] by frame;

        initialize by simp;
        preserve by {
            unfold(vector(owner));
            have i < owner->cap by simp;
            step();
            step();
            close_invariants();
        }
    }

    ensures result == owner->len;
    ensures forall (k: int32) {
        0 <= k and k < owner->len implies owner->data[k] == value
    };
} by {
    execute();
    fold(vector(owner));
    frame();
    have result == owner->len by {
        normalize();
    }
    have forall (k: int32) { 0 <= k and k < owner->len implies owner->data[k] == value } by {
        derive using {
            not at(fill_cells.exit, i) < owner->len;
            forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, owner->data[k]) == at(loop(0).exit, value) };
            at(statement(5).entry, loadable(old(owner->len)));
            at(statement(5).entry, loadable(old(owner->cap)));
            at(statement(5).entry, loadable(old(owner->data)));
            at(statement(5).entry, loadable(old(owner->data[0..owner->cap])));
            at(statement(5).entry, 0) <= at(statement(5).entry, owner->len);
            at(statement(5).entry, owner->len) <= at(statement(5).entry, owner->cap);
            at(statement(5).entry, i) <= at(statement(5).entry, owner->len);
            not at(statement(5).entry, i) < at(statement(5).entry, owner->len);
            at(statement(2).entry, loadable(owner->len));
            at(statement(2).entry, loadable(owner->cap));
            at(statement(2).entry, loadable(owner->data));
            at(statement(2).entry, loadable(owner->data[0..owner->cap]));
            result == owner->len;
        }
    }
    assumption();
    assumption();
    assumption();
}
```

```expect
pass
```
