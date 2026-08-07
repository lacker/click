# branch preserves entry-state memory through a composite view

A structured branch can retain a scalar relation to entry-state memory through
the composite view that makes the old load meaningful.

```c filename=read_first.c
struct buffer {
    int32* data;
};

int32 read_first(struct buffer* owner) {
    return owner->data[0];
}
```

```c filename=advance_composite_old_memory_interface.c
struct buffer {
    int32* data;
};

int32 retain_original(struct buffer* owner, int32 flag) {
    int32 original;
    int32 selected;
    original = read_first(owner);
    if (flag != 0) {
        selected = original;
    } else {
        selected = original;
    }
    return selected;
}
```

```click
resource buffer(owner: struct buffer*) {
    owns owner->data;
    owns owner->data[0..1];
}

verifying "read_first.c";
verifying "advance_composite_old_memory_interface.c";

int32 read_first(struct buffer* owner) {
    views buffer(owner);
    immutable;

    ensures result == owner->data[0] by auto;
}

int32 retain_original(struct buffer* owner, int32 flag) {
    owns buffer(owner);

    ensures result == old(owner->data[0]);
} by {
    execute_until(statement(3));
    observe(buffer(owner));
    branch {
        then {
            step();
        }
        else {
            step();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
