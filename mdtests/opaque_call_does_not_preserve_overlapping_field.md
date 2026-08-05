# opaque call does not preserve an overlapping field

A mutable footprint that covers a field must prevent the caller from treating
its pre-call load as unchanged.

```c filename=overwrite_stable.c
struct owner {
    int32 stable;
    int32 changed;
};

int32 overwrite_stable(struct owner* owner) {
    owner->stable = 8;
    return 0;
}
```

```c filename=opaque_call_does_not_preserve_overlapping_field.c
struct owner {
    int32 stable;
    int32 changed;
};

int32 opaque_call_does_not_preserve_overlapping_field(struct owner* owner) {
    overwrite_stable(owner);
    return owner->stable;
}
```

```click
verifying "overwrite_stable.c";
verifying "opaque_call_does_not_preserve_overlapping_field.c";

int32 overwrite_stable(struct owner* owner) {
    owns object(owner);
    mutable object(owner);
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

int32 opaque_call_does_not_preserve_overlapping_field(struct owner* owner) {
    owns object(owner);
    mutable object(owner);
    ensures result == old(owner->stable);
} by {
    execute();
    frame();
    simp();
}
```

```expect
fail:
```
