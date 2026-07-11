# composite resource owned buffer nested hidden separate gap

This records an open design gap. Direct hidden contained `write(...)`
resources can expose folded-resource `separate(...)` facts, but nested
composite-resource footprints are not summarized across the containing
resource's direct fields.

```c filename=observe_nested_owner_buffer.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 observe_nested_owner_buffer(struct owner* owner) {
    return 0;
}
```

```click
resource backing_buffer(owner: struct owner*) {
    contains write((owner->data)[0..owner->cap]);
}

resource nested_owned_buffer(owner: struct owner*) {
    contains write(owner->len);
    contains write(owner->cap);
    contains write(owner->data);
    contains backing_buffer(owner);
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
}

verifying "observe_nested_owner_buffer.c";

int32 observe_nested_owner_buffer(struct owner* owner) {
    requires nested_owned_buffer(owner);

    ensures separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap])) by auto;
}
```

```expect
fail: separate
```
