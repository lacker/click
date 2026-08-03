# recursive resource requires a guard

Direct recursion is accepted only when the recursive body is conditional.

```c filename=recursive_resource_requires_guard.c
int32 recursive_resource_requires_guard(int32* p) {
    return 0;
}
```

```click
resource endless(p: int32*) {
    contains endless(p);
}

verifying "recursive_resource_requires_guard.c";

int32 recursive_resource_requires_guard(int32* p) {
    ensures result == 0 by auto;
}
```

```expect
fail: composite resource cycle
```
