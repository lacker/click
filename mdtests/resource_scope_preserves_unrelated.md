# Scoped resource opens preserve unrelated persistent resources

Closing a scoped resource must restore its own representation exactly once
without dropping an unrelated resource held by the caller.

```c filename=resource_scope_preserves_unrelated.c
struct object { int32 field; };

int32 preserve_spare(int32 value) {
    return value;
}

int32 resource_scope_preserves_unrelated(struct object* obj, int32 value) {
    obj->field = 1;
    return preserve_spare(value);
}
```

```click
abstract resource spare(value: int32);

resource marker(obj: struct object*) {
    owns obj->field;
}

verifying "resource_scope_preserves_unrelated.c";

int32 preserve_spare(int32 value) {
    consumes spare(value);
    produces spare(value);
    ensures result == value;
} by {
    execute();
    simp();
}

int32 resource_scope_preserves_unrelated(struct object* obj, int32 value) {
    consumes marker(obj);
    consumes spare(value);
    produces marker(obj);
    produces spare(value);
    ensures result == value;
} by {
    open(marker(obj)) {
        step();
    }
    open(marker(obj)) { }
    step();
    execute();
    simp();
}
```

```expect
pass
```
