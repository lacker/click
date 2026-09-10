# a contract that owns nothing allows stack-local updates

This checks that owning nothing means no externally visible memory mutation.
Local stack bookkeeping is not part of the external owned footprint.

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
    ensures returns_one: result == 1 by auto;
}
```

```expect
pass
```
