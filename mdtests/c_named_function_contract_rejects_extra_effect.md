# Pure refinement does not widen a callback's resource or effect interface

The implementation writes a second cell that the named contract neither owns
nor lists as mutable. Stronger pure postconditions cannot compensate for that
larger effect, so the function address does not satisfy the named contract.

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
    mutable output[0..1];
    ensures result == value;
}

int32 store_with_scratch(int32 value, int32* output) {
    owns output[0..2];
    mutable output[0..2];
    ensures result == value;
} by {
    execute();
    frame();
    simp();
}

int32 apply_store(
    int32 (*callback)(int32, int32*),
    int32 value,
    int32* output
) {
    requires Store(callback);
    owns output[0..1];
    mutable output[0..1];
    ensures result == value by auto;
}

int32 extra_effect_caller(int32* output) {
    owns output[0..2];
    mutable output[0..2];
    ensures result == 42 by auto;
}
```

```expect
fail: function `store_with_scratch` does not satisfy named contract `Store`
```
