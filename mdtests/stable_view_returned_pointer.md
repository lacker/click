# A returned C pointer does not escape a caller's independent ownership

Returning a raw pointer value does not return a stable loan. The caller keeps
its own ownership, so it may use the returned pointer for a later write after
the read-only helper returns.

```c filename=stable_view_returned_pointer.c
const int32 *stable_view_returned_pointer(int32 *p) {
    return p;
}

int32 stable_view_returned_pointer_caller(int32 *p) {
    const int32 *returned;
    returned = stable_view_returned_pointer(p);
    p[0] = 7;
    return returned[0];
}
```

```click
verifying "stable_view_returned_pointer.c";

const int32 *stable_view_returned_pointer(int32 *p) {
    requires loadable(p[0..1]);
    ensures result == p;
} by {
    execute();
    simp();
}

int32 stable_view_returned_pointer_caller(int32 *p) {
    owns p[0..1];
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
