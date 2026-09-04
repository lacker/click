# global writes require an explicit mutable footprint

Global storage is not implicitly mutable merely because the C body can write
it. Effect certification must reject a write that the contract does not name.

```c filename=global_effect_requires_mutable.c
int32 counter = 0;

int32 increment() {
    counter = counter + 1;
    return counter;
}
```

```click
verifying "global_effect_requires_mutable.c";

int32 increment() {
    immutable;
    ensures result == old(counter) + 1 by auto;
}
```

```expect
fail: outside the mutable footprint
```
