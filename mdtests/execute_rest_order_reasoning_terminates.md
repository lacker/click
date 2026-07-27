# execute_rest order reasoning terminates

Order facts over a memory-loaded index can enter pointer and alias reasoning
while certifying a batched execution. Re-entering the same condition query
must terminate conservatively instead of overflowing the verifier stack.

```c filename=increment_bounded_counter.c
struct counter {
    int32 value;
    int32 cap;
    int32* data;
};

int32 increment(struct counter* owner) {
    int32 old;
    old = owner->value;
    owner->data[old] = 1;
    owner->value = old + 1;
    return owner->value;
}
```

```click
resource bounded_counter(owner: struct counter*) {
    owns owner->value;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact owner->value == 0;
    fact 1 <= owner->cap;
}

verifying "increment_bounded_counter.c";

int32 increment(struct counter* owner) {
    consumes bounded_counter(owner);
    mutable owner[0..1], (owner->data)[0..1];
    ensures result == owner->value;
} by {
    unfold(bounded_counter(owner));
    have owner->value < owner->cap by simp;
    have 0 <= owner->value by simp;
    have owner->value < 1 by simp;
    execute_rest();
    frame();
    simp();
}
```

```expect
pass
```
