# a quantified load fact does not witness loadability after free

`zero_one` publishes `forall k. 0 <= k and k < 1 implies p[k] == 0`, a
fact about loads in the snapshot before `free(p)`. That fact must not
certify that `result[j]` is loadable in the final snapshot, where the
allocation is gone.

```c filename=zero_one.c
int32 zero_one(int32 p[]) {
    p[0] = 0;
    return 0;
}
```

```c filename=uaf_local.c
int32* uaf_local(int32 fallback[], int32 j) {
    int32* p;
    int32 r;
    p = malloc(4);
    if (p == 0) {
        return fallback;
    }
    r = zero_one(p);
    free(p);
    return p;
}
```

```click
verifying "zero_one.c";
verifying "uaf_local.c";

int32 zero_one(int32 p[]) {
    owns p[0..1];
    mutable p[0..1];
    ensures forall (k: int32) { 0 <= k and k < 1 implies p[k] == 0 };
} by {
    execute();
    frame();
    simp();
}

int32* uaf_local(int32 fallback[], int32 j) {
    requires 0 <= j;
    requires j < 1;
    views fallback[0..1];
    ensures result[j] == result[j];
} by {
    execute();
    simp();
}
```

```expect
fail: loadable
```
