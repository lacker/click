# composite resource loadable fact

This checks that a composite resource can expose a loadability fact. Observing
the resource produces the pure `loadable(...)` fact needed for an indexed read.

```c filename=slice_get.c
int32 slice_get(int32* data, int32 index, int32 len) {
    return data[index];
}
```

```click
resource readable_slice(data: int32*, len: int32) {
    contains read(data[0..len]);
    fact loadable(data[0..len]);
}

verifying "slice_get.c";

int32 slice_get(int32* data, int32 index, int32 len) {
    consumes readable_slice(data, len);
    requires 0 <= index;
    requires index < len;

    ensures result == data[index] by {
        observe(readable_slice(data, len));
        symbolic_execute();
        simp();
    }
}
```

```expect
pass
```
