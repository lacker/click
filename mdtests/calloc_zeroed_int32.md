# calloc supports zeroed int32 allocation authority

The C0 allocation builtin accepts the ordinary two-argument spelling while
retaining the existing symbolic allocation resource and null outcome.

```c filename=calloc_zeroed_int32.c
int32* calloc_zeroed_int32(int32 count) {
    int32* data = calloc(count, sizeof(int32));
    return data;
}
```

```click
resource maybe_zeroed(data: int32*, count: int32) {
    if data != 0 {
        contains allocation(data, count * sizeof(int32));
        owns data[0..count];
    }
}

verifying "calloc_zeroed_int32.c";

int32* calloc_zeroed_int32(int32 count) {
    requires 1 <= count;
    requires count <= 536870911;
    produces maybe_zeroed(result, count);
} by {
    execute();
    fold(maybe_zeroed(result, count));
    simp();
}
```

```expect
pass
```
