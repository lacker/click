# pointer subtraction rejects different pointer objects

Pointer subtraction is undefined when the pointers do not designate the same
array object.

```c filename=c_pointer_cross_block_subtraction.c
int32 distance_local_and_parameter(int32 data[]) {
    int32 local;
    return &local - data;
}
```

```click
verifying "c_pointer_cross_block_subtraction.c";

int32 distance_local_and_parameter(int32 data[]) {
    ensures result == 0;
}
```

```expect
fail: undefined behavior: pointer arithmetic left the pointed-to object
```
