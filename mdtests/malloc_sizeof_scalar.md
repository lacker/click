# runtime allocation accepts scalar sizeof

The existing runtime-sized `int32` allocation model should accept the C ABI
spelling `count * sizeof(int32)` without requiring a magic literal `4`.

```c filename=malloc_sizeof_scalar.c
int32* malloc_sizeof_scalar(int32 count) {
    int32* data;
    data = malloc(count * sizeof(int32));
    return data;
}
```

```click
resource maybe_allocated(data: int32*, count: int32) {
    if data != 0 {
        contains allocation(data, count * sizeof(int32));
        owns data[0..count];
    }
}

verifying "malloc_sizeof_scalar.c";

int32* malloc_sizeof_scalar(int32 count) {
    requires 1 <= count;
    requires count <= 536870911;
    produces maybe_allocated(result, count);
} by {
    execute();
    fold(maybe_allocated(result, count));
    simp();
}
```

```expect
pass
```
