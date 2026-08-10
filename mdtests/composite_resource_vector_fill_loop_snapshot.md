# field-dependent vector storage across loop snapshots

This checks that an owned composite resource whose backing range depends on
owner fields can be used directly through an abstract loop iteration. The loop
mutates only the backing array, so the separate owner metadata and its dependent
backing-range identity remain stable while the numeric loop invariant advances.

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
    ensures result == owner->len;
} by {
    step();
    step();
    loop as fill_cells {
        invariant i >= 0 and i <= owner->len;
        mutable owner->data[0..owner->len] by frame;

        initialize by simp;
        preserve by {
            unfold(vector(owner));
            have i < owner->cap by simp;
            step();
            step();
            have i >= 0 by {
                simp() using {
                    at(statement(3).entry, i) >= 0;
                    at(statement(3).entry, i) < at(statement(3).entry, owner->len);
                }
            }
            have i <= owner->len by {
                simp() using {
                    at(statement(3).entry, i) < at(statement(3).entry, owner->len);
                }
            }
            close_invariants();
        }
    }
    step();
    frame();
    have result == owner->len by {
        normalize();
    }
    assumption();
    assumption();
}
```

```expect
pass
```
