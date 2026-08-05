# writes to a fresh allocation are internal effects

A function may allocate and initialize new storage while promising not to
mutate any memory that existed at function entry. The fresh writes build the
produced resource; they are not changes to the caller's existing footprint.

```c filename=fresh_allocation_writes_are_internal_effects.c
int32* fresh_allocation_writes_are_internal_effects() {
    int32* fresh;
    fresh = malloc(4);
    if (fresh == 0) {
        return fresh;
    }
    fresh[0] = 7;
    return fresh;
}
```

```click
resource maybe_initialized_int32(data: int32*) {
    if data != 0 {
        contains allocation(data, 4);
        owns data[0..1];
        fact data[0] == 7;
    }
}

verifying "fresh_allocation_writes_are_internal_effects.c";

int32* fresh_allocation_writes_are_internal_effects() {
    immutable;
    produces maybe_initialized_int32(result);
} by {
    execute();
    fold(maybe_initialized_int32(result));
    frame();
    simp();
}
```

```expect
pass
```
