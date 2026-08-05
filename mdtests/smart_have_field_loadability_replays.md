# smart have retains field-derived loadability

A quantified smart `have` over a field-derived array must emit a certificate
that replays after neighboring metadata fields have been materialized and an
unrelated allocation result has been refined.

```c filename=smart_have_field_loadability_replays.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 smart_have_field_loadability_replays(struct buffer* owner) {
    int32 old_capacity;
    int32* old_data;
    int32* fresh;

    old_capacity = owner->cap;
    old_data = owner->data;
    fresh = malloc(4);
    if (fresh == 0) {
        return 0;
    }
    free(fresh);
    return 1;
}
```

```click
resource replay_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact owner->cap <= 536870910;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

verifying "smart_have_field_loadability_replays.c";

int32 smart_have_field_loadability_replays(struct buffer* owner) {
    owns replay_buffer(owner);
    ensures result == 0 or result == 1;
} by {
    unfold(replay_buffer(owner));
    execute_until(statement(6));
    have owner->len <= owner->cap by simp;
    if fresh == 0 {
        have forall (k: int32) {
            0 <= k and k < old(owner->len) implies
                owner->data[k] == (old(owner->data))[k]
        } by simp;
        execute();
        fold(replay_buffer(owner));
        simp();
    } else {
        execute();
        fold(replay_buffer(owner));
        simp();
    }
}
```

```expect
pass
```
