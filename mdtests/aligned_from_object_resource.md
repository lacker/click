# a complete-object clause carries its alignment

`object(p)` for a struct type states that a live object of that type is at
`p`, and such an object is placed at the type's alignment. The clause
therefore carries `aligned(p, alignof(struct))`: a caller proves it for a
required object, the function proves it for a produced one, and the
function relies on it for an object it receives.

```c filename=aligned_from_object_resource.c
struct pair {
    int32 a;
    int64 b;
};

int32 object_is_aligned(struct pair *p) {
    return ((unsigned long)p & 7) == 0;
}

struct pair *pass_through(struct pair *p) {
    return p;
}
```

```click
verifying "aligned_from_object_resource.c";

int32 object_is_aligned(struct pair* p) {
    requires p != 0;
    views object(p);
    ensures result == 1;
} by {
    execute();
    simp();
}

struct pair* pass_through(struct pair* p) {
    consumes object(p);
    produces object(result);
    ensures result == p;
} by {
    execute();
    simp();
}
```

```expect
pass
```
