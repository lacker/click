# fill3 rejects a false memory postcondition

This checks that `auto` reports the actual final memory value when a memory
postcondition is false.

```c filename=fill3_bad_memory.c
int32 fill3_bad_memory(int32* p) {
    int32 i;
    i = 0;
    while (i < 3) {
        p[i] = i;
        i = i + 1;
    }
    return p[2];
}
```

```click
verifying "fill3_bad_memory.c";

int32 fill3_bad_memory(int32* p) {
    requires valid_range(p, 12);
    ensures third: p[2] == 3 by auto;
}
```

```expect
fail: left side evaluated to Int32(Constant(2))
```
