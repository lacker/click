# Iterated ownership refuses a guard over cells the body does not own

The guard decides which elements the iterated clause holds, so it must be
stable while the enclosing resource is folded. It is stable exactly when the
same body owns every guard cell it reads. Here `flags` is only a parameter,
so anyone holding `flags` could change which `data` cells the folded resource
claims; the declaration is refused. The accepted form is
[`iterated_ownership_declaration.md`](iterated_ownership_declaration.md).

```c filename=iterated_ownership_rejects_unowned_guard.c
void keep(int32* data, int32* flags, int32 capacity) {}
```

```click
resource loose_cells(data: int32*, flags: int32*, capacity: int32) {
    forall (k: int32) where 0 <= k and k < capacity {
        if flags[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "iterated_ownership_rejects_unowned_guard.c";

void keep(int32* data, int32* flags, int32 capacity) {
    owns loose_cells(data, flags, capacity);
} by {
    execute();
    simp();
}
```

```expect
fail: the guard must read only cells the same body owns
```
