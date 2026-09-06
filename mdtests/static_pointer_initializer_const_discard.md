# static pointer initializers reject discarded pointee constness

Taking the address of a const object cannot initialize a pointer whose type
would permit writes through it.

```c filename=const_pointer.c
const int32 target = 3;
int32 *target_alias = &target;

int32 read_target_alias() {
    return *target_alias;
}
```

```click
verifying "const_pointer.c";

int32 read_target_alias() {
    ensures result == 3;
}
```

```expect
fail: cannot discard const qualification
```
