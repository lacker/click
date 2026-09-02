# conditional deallocation survives a branch interface

The branch interface must preserve a heap allocation whose lifetime depends on
the branch result. The folded conditional resource is empty on the freed arm
and owns the allocation on the retained arm.

```c filename=conditional_deallocation_join.c
int32 conditional_deallocation_join(int32* p, int32 error) {
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
resource allocated(p: int32*) {
    contains allocation(p, 4);
    owns p[0..1];
}

resource maybe_allocated(p: int32*, error: int32) {
    if error == 0 {
        contains allocation(p, 4);
        owns p[0..1];
    }
}

verifying "conditional_deallocation_join.c";

int32 conditional_deallocation_join(int32* p, int32 error) {
    consumes allocated(p);
    produces maybe_allocated(p, error);
} by {
    unfold(allocated(p));
    step();
    branch {
        ensuring {
            owns maybe_allocated(p, error);
        }
        then {
            step();
            step();
            fold(maybe_allocated(p, error));
        }
        else {
            step();
            fold(maybe_allocated(p, error));
        }
    }
    step();
    simp();
}
```

```expect
pass
```
