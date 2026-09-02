# relational comparison rejects different pointer objects

Relational comparison is undefined when the pointers do not designate the
same array object.

```c filename=c_pointer_cross_block_comparison.c
int32 compare_local_and_parameter(int32 data[]) {
    int32 local;
    return &local < data;
}
```

```click
verifying "c_pointer_cross_block_comparison.c";

int32 compare_local_and_parameter(int32 data[]) {
    ensures result == 0;
}
```

```expect
fail: undefined behavior: pointer arithmetic left the pointed-to object
```
