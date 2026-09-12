# Scoped resource opens preserve unrelated persistent resources

Closing a scoped resource must restore its own representation exactly once
without dropping an unrelated resource held by the caller.

```c filename=resource_scope_preserves_unrelated.c
int32 resource_scope_preserves_unrelated(int32 value) {
    return value;
}
```

```click
abstract resource spare(value: int32);

resource marker(value: int32) {
    fact value == value;
}

verifying "resource_scope_preserves_unrelated.c";

int32 resource_scope_preserves_unrelated(int32 value) {
    consumes marker(value);
    consumes spare(value);
    ensures result == value;
} by {
    open(marker(value)) { }
    open(marker(value)) { }
    execute();
    simp();
}
```

```expect
pass
```
