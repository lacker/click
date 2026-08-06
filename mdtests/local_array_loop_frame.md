# local array loop frame verifies stack array effects

This checks that a loop can state an explicit per-step mutable footprint over a
local array object.

```c filename=local_array_loop_frame.c
int32 local_array_loop_frame() {
    int32 a[3];
    int32 i;
    i = 0;
    while (i < 3) {
        a[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "local_array_loop_frame.c";

int32 local_array_loop_frame() {
    ensures returns_count: result == 3;
} by {
    step();
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 3;
        step {
            mutable a[i..i + 1] by frame;
        }
    }
    step();
    simp();
}
```

```expect
pass
```
