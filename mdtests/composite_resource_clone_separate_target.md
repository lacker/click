# Clone a composite resource into separate storage

Resolving source-field loads while materializing a separate target must use
nonrecursive alias reasoning. General pointer equality may itself inspect
memory, so memory-load resolution uses bounded structural rules for direct
equality facts, explicit separation, common-base offsets, and unchanged loads.

```c filename=clone_cursor.c
struct cursor {
    int32 pos;
    int32 len;
    int32* data;
};

int32 clone_cursor(struct cursor* target, struct cursor* source) {
    target->pos = source->pos;
    target->len = source->len;
    target->data = source->data;
    return target->pos;
}
```

```click
resource owned_cursor(owner: struct cursor*) {
    owns owner->pos;
    owns owner->len;
    owns owner->data;
    views (owner->data)[0..owner->len];
    fact 0 <= owner->pos;
    fact owner->pos <= owner->len;
    fact separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->len])
    );
}

verifying "clone_cursor.c";

int32 clone_cursor(struct cursor* target, struct cursor* source) {
    requires separate(memory(target[0..4]), memory(source[0..4]));
    requires separate(
        memory(target[0..4]),
        memory((source->data)[0..source->len])
    );
    consumes target[0..4];
    views owned_cursor(source);
    mutable target[0..4];
    produces owned_cursor(target);
    ensures result == source->pos;
    ensures target->pos == source->pos;
    ensures target->len == source->len;
    ensures target->data == source->data;
} by {
    observe(owned_cursor(source));
    execute_rest();
    fold(owned_cursor(target));
    frame();
    simp();
}
```

```expect
pass
```
