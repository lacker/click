# Grouped function proof

A trailing proof block proves all resource and pure postconditions from one
execution pass. `simp()` closes the postconditions from the resulting shared
state; the write bound comes from the contract's ownership, with no separate
effect goal to discharge.

```c filename=grouped_function_proof.c
int32 set_first(int32 p[], int32 value) {
    p[0] = value;
    return p[0];
}
```

```click
verifying "grouped_function_proof.c";

int32 set_first(int32 p[], int32 value) {
    consumes p[0..1];
    produces p[0..1];
    ensures result == value;
    ensures p[0] == value;
} by {
    execute();
    simp();
}
```

```expect
pass
```
