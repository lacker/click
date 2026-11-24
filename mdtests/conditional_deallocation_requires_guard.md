# conditional deallocation requires a lifetime guard

A branch interface cannot hide a path-dependent heap lifetime behind an
unrelated resource. The retained allocation must be represented by the
resource exported at the join.

```c filename=conditional_deallocation_requires_guard.c
int32 conditional_deallocation_requires_guard(int32* p, int32 error) {
    int32 result;
    if (error != 0) {
        free(p);
        result = -1;
    } else {
        result = 0;
    }
    return result;
}
```

```click
abstract resource permit();

resource allocated(p: int32*) {
    owns allocation(p, 4);
    owns p[0..1];
}

verifying "conditional_deallocation_requires_guard.c";

int32 conditional_deallocation_requires_guard(int32* p, int32 error) {
    consumes allocated(p);
    owns permit();
} by {
    unfold(allocated(p));
    step();
    branch ensuring {
        owns permit();
    } {
        true => {
            step();
            step();
        }
        false => {
            step();
        }
    }
    step();
    close();
}
```

```expect
fail: arm-sensitive owned resource
```
