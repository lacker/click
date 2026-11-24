# a quantified load fact does not witness viewability after free

`zero_one` publishes `forall k. 0 <= k and k < 1 implies p[k] == 0`, a
fact about loads in the state before `free(p)`. That fact must not
certify that `result[j]` is viewable in the final state, where the
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
    owns uninitialized(p[0..1]);
    ensures forall (k: int32) { 0 <= k and k < 1 implies p[k] == 0 };
}

int32* uaf_local(int32 fallback[], int32 j) {
    requires 0 <= j;
    requires j < 1;
    views fallback[0..1];
    ensures defined(result[j]);
} by {
    step_until(statement(3).entry);
    if p == 0 {
        step_until(function.exit);
        have j == 0;
        have defined(result[j]) by {
            rewrite(j, 0);
            close();
        }
    } else {
        step();
        have separate(memory((p as (uint8*))[0..4]), memory(fallback[0..1])) by { close(); }
        step();
        step_until(function.exit);
        close();
    }
}
```

```expect
fail: `ensures defined(result[j])` failed for `uaf_local.ensures_0` path 1: unclosed goal: defined(result[j])
```
