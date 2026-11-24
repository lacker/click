# Pure refinement does not widen a callback's ownership interface

The implementation owns, and writes, a second cell that the named contract does
not own. Stronger pure postconditions cannot compensate for that wider
ownership, so the function address does not satisfy the named contract.

```c filename=extra_effect_step.c
int32 store_with_scratch(int32 value, int32* output) {
    output[0] = value;
    output[1] = value;
    return value;
}

int32 apply_store(
    int32 (*callback)(int32, int32*),
    int32 value,
    int32* output
) {
    return callback(value, output);
}

int32 extra_effect_caller(int32* output) {
    return apply_store(&store_with_scratch, 42, output);
}
```

```click
verifying "extra_effect_step.c";

contract int32 Store(int32 value, int32* output) {
    owns output[0..1];
    ensures result == value;
}

int32 store_with_scratch(int32 value, int32* output) {
    owns output[0..2];
    ensures result == value;
}

int32 apply_store(
    int32 (*callback)(int32, int32*),
    int32 value,
    int32* output
) {
    requires Store(callback);
    owns output[0..1];
    ensures result == value;
}

theorem proposed_store_with_scratch_contract() {
    ensures Store(&store_with_scratch) by {
        unfold(Store(&store_with_scratch));
        close();
    }
}

int32 extra_effect_caller(int32* output) {
    owns output[0..2];
    ensures result == 42;
} by {
    apply(proposed_store_with_scratch_contract());
}
```

```expect
fail: contract-refinement proof does not establish `Store(&store_with_scratch)`
```
