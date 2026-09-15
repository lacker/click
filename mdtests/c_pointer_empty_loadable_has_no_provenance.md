# empty loadability does not establish pointer object provenance

An empty `loadable` range is vacuously true even for a null pointer. It cannot
justify a relational pointer operation that requires an actual array object.

```c filename=c_pointer_empty_loadable_has_no_provenance.c
int32 self_order(int32 *pointer) {
    return pointer <= pointer;
}
```

```click
verifying "c_pointer_empty_loadable_has_no_provenance.c";

int32 self_order(int32* pointer) {
    requires loadable(pointer[0..0]);
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: pointer arithmetic left the pointed-to object
```
