# nonzero integer is not an implicit pointer

Supporting C's null pointer constant does not permit general integer-to-pointer
conversion.

```c filename=c_nonzero_integer_rejected_as_pointer.c
int32* invalid_pointer() {
    return 1;
}
```

```click
verifying "c_nonzero_integer_rejected_as_pointer.c";

int32* invalid_pointer() {
    ensures result != 0 by auto;
}
```

```expect
fail: runtime error: type mismatch
```
