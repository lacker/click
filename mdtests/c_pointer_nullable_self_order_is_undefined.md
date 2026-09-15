# a nullable pointer does not automatically share an object with itself

An object pointer parameter may be null. Reusing the same parameter proves
pointer-value identity, but it does not prove that an array object exists for
a relational comparison.

```c filename=c_pointer_nullable_self_order_is_undefined.c
int32 self_order(int32 *pointer) {
    return pointer <= pointer;
}
```

```click
verifying "c_pointer_nullable_self_order_is_undefined.c";

int32 self_order(int32* pointer) {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: pointer arithmetic left the pointed-to object
```
