# conditional resource unfold requires a decided guard

An explicit `unfold` must know whether the guarded body is present or empty.

```c filename=conditional_resource_unfold_requires_decided_guard.c
int32 guarded_value(int32* p) {
    return 0;
}
```

```click
resource guarded_cell(p: int32*) {
    if p != 0 {
        owns p[0..1];
    }
}

verifying "conditional_resource_unfold_requires_decided_guard.c";

int32 guarded_value(int32* p) {
    owns guarded_cell(p);
    ensures result == 0;
} by {
    unfold(guarded_cell(p));
    execute();
    fold(guarded_cell(p));
    simp();
}
```

```expect
fail: condition is undecided
```
