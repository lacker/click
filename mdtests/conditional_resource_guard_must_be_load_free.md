# conditional resource guard must be load-free

A resource guard selects which permissions exist, so it cannot inspect memory
whose permission would itself depend on that selection.

```c filename=conditional_resource_guard_must_be_load_free.c
int32 guarded_value(int32* p) {
    return 0;
}
```

```click
resource guarded_cell(p: int32*) {
    if p[0] != 0 {
        owns p[0..1];
    }
}

verifying "conditional_resource_guard_must_be_load_free.c";

int32 guarded_value(int32* p) {
    owns guarded_cell(p);
    ensures result == 0 by auto;
}
```

```expect
fail: must be load-free
```
