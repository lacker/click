# field-state composite round trip

Verified opaque calls may change a metadata fact while preserving the same
nested, field-dependent storage resource. Certification must process each
call's effect summary before checking its postconditions against earlier state
facts.

```c filename=composite_resource_field_state_roundtrip.c
struct state_owner {
    int32 state;
    int32* data;
};

int32 set_one(struct state_owner* owner) {
    owner->state = 1;
    return owner->state;
}
```

```c filename=composite_resource_field_state_set_zero.c
struct state_owner {
    int32 state;
    int32* data;
};

int32 set_zero(struct state_owner* owner) {
    owner->state = 0;
    return owner->state;
}
```

```c filename=composite_resource_field_state_roundtrip_pipeline.c
struct state_owner {
    int32 state;
    int32* data;
};

int32 field_state_roundtrip(struct state_owner* owner) {
    int32 first;
    int32 ignored;
    first = set_one(owner);
    ignored = set_zero(owner);
    return first;
}
```

```click
resource owned_state_storage(data: int32*) {
    owns data[0..1];
}

resource zero_state(owner: struct state_owner*) {
    owns owner->state;
    owns owner->data;
    contains owned_state_storage(owner->data);
    fact owner->state == 0;
}

resource one_state(owner: struct state_owner*) {
    owns owner->state;
    owns owner->data;
    contains owned_state_storage(owner->data);
    fact owner->state == 1;
}

verifying "composite_resource_field_state_roundtrip.c";
verifying "composite_resource_field_state_set_zero.c";
verifying "composite_resource_field_state_roundtrip_pipeline.c";

int32 set_one(struct state_owner* owner) {
    consumes zero_state(owner);
    mutable owner->state;
    produces one_state(owner);

    ensures result == 1;
    ensures owner->state == 1;
    ensures owner->data == old(owner->data);
} by {
    unfold(zero_state(owner));
    execute();
    fold(one_state(owner));
    frame();
    simp();
}

int32 set_zero(struct state_owner* owner) {
    consumes one_state(owner);
    mutable owner->state;
    produces zero_state(owner);

    ensures result == 0;
    ensures owner->state == 0;
    ensures owner->data == old(owner->data);
} by {
    unfold(one_state(owner));
    execute();
    fold(zero_state(owner));
    frame();
    simp();
}

int32 field_state_roundtrip(struct state_owner* owner) {
    consumes zero_state(owner);
    mutable owner->state;
    produces zero_state(owner);

    ensures result == 1;
    ensures owner->state == 0;
    ensures owner->data == old(owner->data);
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
