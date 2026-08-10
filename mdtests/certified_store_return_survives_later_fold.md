# certified stores pair a final load with the stored return value

Proof replay may retain a return as a load from final memory while fresh
kernel certification simplifies it to the value stored earlier. A later
disjoint store and folding the raw fields back into a composite resource must
not make those two certified executions disagree.

```c filename=certified_store_return_survives_later_fold.c
struct pair {
    int32 value;
    int32 other;
};

int32 increment_and_clear(struct pair *pair) {
    int32 next = pair->value + 1;
    pair->value = next;
    pair->other = 0;
    return pair->value;
}
```

```click
resource owned_pair(pair: struct pair*) {
    owns object(pair);
}

verifying "certified_store_return_survives_later_fold.c";

int32 increment_and_clear(struct pair* pair) {
    requires pair->value < 2147483647;
    consumes owned_pair(pair);
    mutable pair->value, pair->other;
    produces owned_pair(pair);

    ensures result == old(pair->value) + 1;
} by {
    unfold(owned_pair(pair));
    execute();
    fold(owned_pair(pair));
    frame();
    simp();
}
```

```expect
pass
```
