# immutable allows stack-local updates

This checks that `immutable` means no externally visible memory mutation. Local
stack bookkeeping is not part of the external mutable footprint.

```c filename=immutable_stack_locals.c
int32 immutable_stack_locals() {
    int32 i;
    i = 0;
    i = i + 1;
    return i;
}
```

```click
verifying "immutable_stack_locals.c";

int32 immutable_stack_locals() {
    immutable by frame;
    ensures returns_one: result == 1 by auto;
}
```

```expect
pass
```
