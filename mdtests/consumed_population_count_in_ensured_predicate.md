# consumed populations are visible to ensured predicates

A symbolic resource consumption and a matching C update preserve a predicate
that relates concrete state to the post-state population count. Independent
contract certification must use the same checked population transition as the
explicit proof.

```c filename=consume_population.c
struct owner {
    int32 used;
    int32 capacity;
};

void consume_population(struct owner* owner, int32 amount) {
    owner->capacity = owner->capacity - amount;
}
```

```click
resource slot(owner: struct owner*) {
    views object(owner);
}

abstract resource item(owner: struct owner*, id: int32);

predicate valid_capacity(owner: struct owner*) {
    0 <= owner->used and
    owner->used == count(item(owner, _)) and
    owner->capacity == owner->used + count(slot(owner))
}

verifying "consume_population.c";

void consume_population(struct owner* owner, int32 amount) {
    requires valid_capacity(owner);
    requires 0 <= amount;
    requires amount <= count(slot(owner));
    requires defined(owner->capacity - amount);
    owns object(owner);
    consumes amount of slot(owner);
    mutable owner->capacity;

    ensures valid_capacity(owner);
} by {
    unfold(valid_capacity);
    execute();
    frame();
    simp();
}
```

```expect
pass
```
