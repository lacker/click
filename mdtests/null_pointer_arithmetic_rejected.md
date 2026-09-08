# displacing a null pointer is undefined behaviour

Additive pointer arithmetic is defined only for a pointer that designates an
element of an array object or one past its end (C11 6.5.6p8). A null pointer
designates no object, so the sum has no value: without the check the displaced
pointer carried a nonzero offset, compared unequal to null, and decided a
branch C leaves undefined.

```c filename=null_pointer_arithmetic_rejected.c
int32 null_pointer_arithmetic_rejected() {
    int32* start = 0;
    int32* next = start + 1;
    if (next == 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "null_pointer_arithmetic_rejected.c";

int32 null_pointer_arithmetic_rejected() {
    ensures result == 0;
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
