# global writes require explicit ownership

Global storage is not implicitly owned merely because the C body can write it.
Contract certification must reject a write to storage the contract does not
own.

```c filename=global_write_requires_ownership.c
int32 counter = 0;

int32 increment() {
    counter = counter + 1;
    return counter;
}
```

```click
verifying "global_write_requires_ownership.c";

int32 increment() {
    requires counter < 1000;
    ensures result == old(counter) + 1 by auto;
}
```

```expect
fail: outside the mutable footprint
```
