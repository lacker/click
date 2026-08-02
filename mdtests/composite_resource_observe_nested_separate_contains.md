# composite resource observe nested separate contains

This checks that a chain of `observe(...)` steps exposes direct `contains(...)`
and `separate(...)` facts for nested memory resources.

```c filename=observe_nested_separate_contains.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 observe_nested_separate_contains(struct owner* owner) {
    return 0;
}
```

```click
resource backing_buffer(owner: struct owner*) {
    owns (owner->data)[0..owner->cap];
}

resource nested_owned_buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    contains backing_buffer(owner);
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
}

verifying "observe_nested_separate_contains.c";

int32 observe_nested_separate_contains(struct owner* owner) {
    consumes nested_owned_buffer(owner);

    ensures separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap])) by {
        observe(nested_owned_buffer(owner));
        observe(backing_buffer(owner));
        execute();
        simp();
    }
}
```

```expect
pass
```
