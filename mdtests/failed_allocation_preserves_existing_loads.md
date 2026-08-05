# failed allocation preserves existing loads

Registering and resolving a fresh allocation must not disturb a separately
owned buffer. This covers both the null branch and a successful allocation
that is freed without initializing it.

```c filename=failed_allocation_preserves_existing_loads.c
int32 failed_allocation_preserves_existing_loads(int32 data[], int32 length) {
    int32* fresh;
    fresh = malloc(length * 4);
    if (fresh == 0) {
        return data[0];
    }
    free(fresh);
    return data[0];
}
```

```click
verifying "failed_allocation_preserves_existing_loads.c";

int32 failed_allocation_preserves_existing_loads(int32 data[], int32 length) {
    requires 1 <= length;
    requires length <= 536870911;
    owns data[0..length];
    ensures result == old(data[0]);
    ensures forall (k: int32) {
        0 <= k and k < length implies data[k] == old(data[k])
    };
} by {
    execute();
    simp();
}
```

```expect
pass
```
