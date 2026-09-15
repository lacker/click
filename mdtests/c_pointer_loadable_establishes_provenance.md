# nonempty loadability establishes pointer object provenance

A nonempty `loadable` proposition says that at least one byte belongs to the
pointer's live object. It therefore rules out a null object base and makes
self-ordering and self-subtraction defined without requiring memory authority.

```c filename=c_pointer_loadable_establishes_provenance.c
int32 self_order(int32 *pointer) {
    return pointer <= pointer;
}

int32 self_distance(int32 *pointer) {
    return pointer - pointer;
}
```

```click
verifying "c_pointer_loadable_establishes_provenance.c";

int32 self_order(int32* pointer) {
    requires loadable(pointer[0..1]);
    ensures result == 1;
} by { execute(); simp(); }

int32 self_distance(int32* pointer) {
    requires loadable(pointer[0..1]);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
