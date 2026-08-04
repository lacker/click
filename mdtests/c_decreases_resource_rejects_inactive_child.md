# an inactive resource body has no structural child

The empty witness may still satisfy an ordinary recursive partial contract.
It cannot be treated as containing the guarded child merely because that child
appears syntactically in the resource definition.

```c filename=c_decreases_resource_rejects_inactive_child.c
int32 empty_repeat(int32 active) {
    int32 result;
    result = empty_repeat(0);
    return result;
}
```

```click
resource guarded(active: int32) {
    if active != 0 {
        contains guarded(0);
    }
}

verifying "c_decreases_resource_rejects_inactive_child.c";

int32 empty_repeat(int32 active) {
    decreases resource guarded(active);
    views guarded(active);
    immutable;

    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}
```

```expect
fail: requires the instantiated `guarded` guard as an exact function precondition
```
