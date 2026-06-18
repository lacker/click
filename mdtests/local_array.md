# local array verifies stack array storage

This checks that C0 local arrays are modeled as stack memory objects. The array
name decays to a pointer for indexing, while the array itself is not a scalar
pointer variable.

```c filename=local_array.c
int32 local_array_roundtrip() {
    int32 a[3];
    a[0] = 5;
    a[1] = 7;
    return a[1];
}
```

```click
verifying "local_array.c";

int32 local_array_roundtrip() {
    ensures returns_second: result == 7 by auto;
}
```

```expect
pass
```
