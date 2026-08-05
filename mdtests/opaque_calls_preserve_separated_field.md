# opaque calls preserve a separated field

Two opaque helpers mutate one struct field. The adjacent field is outside both
mutable footprints, so its load remains equal to the caller-entry load without
any save-and-restore assignment in C.

```c filename=increment_changed.c
struct owner {
    int32 stable;
    int32 changed;
};

int32 increment_changed(struct owner* owner) {
    owner->changed = 1;
    return 0;
}
```

```c filename=clear_changed.c
struct owner {
    int32 stable;
    int32 changed;
};

int32 clear_changed(struct owner* owner) {
    owner->changed = 0;
    return 0;
}
```

```c filename=opaque_calls_preserve_separated_field.c
struct owner {
    int32 stable;
    int32 changed;
};

int32 opaque_calls_preserve_separated_field(struct owner* owner) {
    increment_changed(owner);
    clear_changed(owner);
    return owner->stable;
}
```

```click
verifying "increment_changed.c";
verifying "clear_changed.c";
verifying "opaque_calls_preserve_separated_field.c";

int32 increment_changed(struct owner* owner) {
    owns owner->changed;
    mutable owner->changed;
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

int32 clear_changed(struct owner* owner) {
    owns owner->changed;
    mutable owner->changed;
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

int32 opaque_calls_preserve_separated_field(struct owner* owner) {
    owns object(owner);
    mutable owner->changed;
    ensures result == old(owner->stable);
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
