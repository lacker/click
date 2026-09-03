# loop back edge cannot resurrect a consumed resource

```c filename=take.c
int32 take(int32* p) {
    return 0;
}
```

```c filename=loop_resource_lifetime_join.c
int32 loop_resource_lifetime_join(int32* p) {
    int32 i;
    int32 status;
    i = 0;
    status = 0;
    while (i < 2) {
        status = take(p);
        i = i + 1;
    }
    p[0] = 7;
    return status;
}
```

```click
verifying "loop_resource_lifetime_join.c";
verifying "take.c";

int32 take(int32* p) {
    consumes p[0..1];
    ensures result == 0 by auto;
}

int32 loop_resource_lifetime_join(int32* p) {
    owns p[0..1];
    mutable p[0..1];
    ensures p[0] == 7;
} by {
    step();
    step();
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 1;
        mutable p[0..1] by frame;
    }
    step();
    step();
    frame();
    simp();
}
```

```expect
fail: resource ownership
```
