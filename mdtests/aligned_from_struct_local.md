# a struct local is aligned for its layout

Taking the address of a struct local is alignment evidence for the layout's
alignment, not for the byte-array type that carries the object's storage.

```c filename=aligned_from_struct_local.c
struct pair {
    int32 a;
    int64 b;
};

int32 struct_local_is_aligned() {
    struct pair local;
    return ((unsigned long)&local & 7) == 0;
}

int32 struct_local_pointer_is_aligned() {
    struct pair local;
    struct pair *p = &local;
    return ((unsigned long)p & 7) == 0;
}
```

```click
verifying "aligned_from_struct_local.c";

int32 struct_local_is_aligned() {
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 struct_local_pointer_is_aligned() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
