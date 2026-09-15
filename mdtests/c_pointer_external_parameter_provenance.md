# pointer parameter address space is not object provenance

Independent pointer parameters may alias, but that shared address space does
not prove that they point into one C array object. A helper contract cannot
hide the undefined behavior of ordering pointers to distinct caller locals.

```c filename=c_pointer_external_parameter_provenance.c
int32 compare(int32 *left, int32 *right) {
    return left < right;
}

int32 compare_locals(void) {
    int32 left = 1;
    int32 right = 2;
    return compare(&left, &right);
}
```

```click
verifying "c_pointer_external_parameter_provenance.c";

int32 compare(int32* left, int32* right) {
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 compare_locals() {
    ensures result == 0 or result == 1;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: pointer arithmetic left the pointed-to object
```
