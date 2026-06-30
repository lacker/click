# local array rejects direct assignment

This checks that C0 does not model a local array as a hidden pointer variable.
The array name can decay in rvalue contexts, but the array object itself cannot
be assigned.

```c filename=local_array_rejects_assignment.c
int32 local_array_rejects_assignment(int32* p) {
    int32 a[3];
    a = p;
    return 0;
}
```

```click
verifying "local_array_rejects_assignment.c";

int32 local_array_rejects_assignment(int32* p) {
    ensures returns_zero: result == 0 by auto;
}
```

```expect
fail: runtime error: type mismatch
```
