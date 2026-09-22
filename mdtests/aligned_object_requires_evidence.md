# requiring a complete object needs alignment evidence at the call

A required `object(p)` carries `aligned(p, alignof(struct))`, so a caller
that holds the object's bytes without knowing the pointer's alignment cannot
pass it.

```c filename=aligned_object_requires_evidence.c
struct pair {
    int32 a;
    int64 b;
};

int32 object_is_aligned(struct pair *p) {
    return ((unsigned long)p & 7) == 0;
}

int32 forward(struct pair *p) {
    return object_is_aligned(p);
}
```

```click
verifying "aligned_object_requires_evidence.c";

resource pair_storage(p: struct pair*) {
    views object(p);
    fact aligned(p, 8);
}


int32 object_is_aligned(struct pair* p) {
    requires p != 0;
    views pair_storage(p);
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 forward(struct pair* p) {
    requires p != 0;
    views p[0..4];
    ensures result == 1;
} by {
    fold(pair_storage(p));
    execute();
    simp();
}
```

```expect
fail: requires an exact body fact
```
