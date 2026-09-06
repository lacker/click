# file-scope and static objects are aligned for their type

The compiler places a file-scope or static object at its type's alignment.
That alignment is intrinsic to the object's block and is recorded once when
the block is created, so no path fact is minted on the implicit address-of
of every read.

```c filename=aligned_from_globals_and_statics.c
struct pair {
    int32 a;
    int64 b;
};

int32 counter;
struct pair shared;

int32 global_is_aligned() {
    return ((unsigned long)&counter & 3) == 0;
}

int32 global_struct_is_aligned() {
    return ((unsigned long)&shared & 7) == 0;
}

int32 static_is_aligned() {
    static int32 slot;
    return ((unsigned long)&slot & 3) == 0;
}
```

```click
verifying "aligned_from_globals_and_statics.c";

int32 global_is_aligned() {
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 global_struct_is_aligned() {
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 static_is_aligned() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
