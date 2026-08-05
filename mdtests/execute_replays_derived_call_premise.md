# execute replays a derived opaque-call premise

The caller knows `length <= capacity` and passes `capacity + 1` to an opaque
helper. `execute()` must retain a replayable derivation of the helper's weaker
requirement even when the two field loads acquire different materialized
memory-snapshot spellings.

```c filename=accept_larger_capacity.c
int32 accept_larger_capacity(int32 length, int32 capacity) {
    return length;
}
```

```c filename=execute_replays_derived_call_premise.c
struct owner {
    int32 length;
    int32 capacity;
};

int32 execute_replays_derived_call_premise(struct owner* owner) {
    int32 accepted;
    accepted = accept_larger_capacity(owner->length, owner->capacity + 1);
    return accepted;
}
```

```click
verifying "accept_larger_capacity.c";
verifying "execute_replays_derived_call_premise.c";

int32 accept_larger_capacity(int32 length, int32 capacity) {
    requires length <= capacity;
    ensures result == length;
} by auto;

int32 execute_replays_derived_call_premise(struct owner* owner) {
    requires owner->length <= owner->capacity;
    requires owner->capacity < 2147483647;
    views object(owner);
    immutable;
    ensures result == owner->length;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
