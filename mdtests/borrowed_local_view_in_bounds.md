# a borrowed view that fits the caller's local still needs no resource clause

The positive half of `borrowed_local_view_bounds_rejected.md`. A callee that
views exactly what the caller's stack object holds is called without the
caller spelling any resource clause.

```c filename=borrowed_local_view_in_bounds.c
int32 third(int32* values) {
    return values[2];
}

int32 borrowed_local_view_in_bounds() {
    int32 triple[3];
    triple[0] = 1;
    triple[1] = 2;
    triple[2] = 3;
    return third(triple);
}
```

```click
verifying "borrowed_local_view_in_bounds.c";

int32 third(int32* values) {
    views values[0..3];
    ensures result == values[2] by auto;
}

int32 borrowed_local_view_in_bounds() {
    ensures result == 3 by auto;
}
```

```expect
pass
```
