# Pure callback refinement preserves an exact resource and effect interface

Behavioral variance applies to the pure clauses while the callback's resource
transition and mutable footprint remain exact. Those exact parts are compared
after binding both interfaces to the same symbolic arguments, so parameter
spelling does not matter there either.

```c filename=resource_refining_step.c
int32 store_increment(int32 value, int32* destination) {
    destination[0] = value + 1;
    return value + 1;
}

int32 apply_store_step(
    int32 (*callback)(int32, int32*),
    int32 input,
    int32* output
) {
    return callback(input, output);
}

int32 resource_refining_step_caller(int32* output) {
    return apply_store_step(&store_increment, 41, output);
}
```

```click
verifying "resource_refining_step.c";

contract int32 StoreStep(int32 input, int32* output) {
    requires 0 <= input;
    requires input <= 100;
    owns output[0..1];
    mutable output[0..1];
    ensures result == input + 1;
}

int32 store_increment(int32 value, int32* destination) {
    requires -100 <= value;
    requires value <= 1000;
    owns destination[0..1];
    mutable destination[0..1];
    ensures result == value + 1;
    ensures value < result;
} by {
    execute();
    frame();
    simp();
}

int32 apply_store_step(
    int32 (*callback)(int32, int32*),
    int32 input,
    int32* output
) {
    requires StoreStep(callback);
    requires 0 <= input;
    requires input <= 100;
    owns output[0..1];
    mutable output[0..1];
    ensures result == input + 1;
} by {
    execute();
    frame();
    simp();
}

int32 resource_refining_step_caller(int32* output) {
    owns output[0..1];
    mutable output[0..1];
    ensures result == 42;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
