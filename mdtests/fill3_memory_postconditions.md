# fill3 proves final memory contents

This checks that `ensures` can talk about post-call memory, not just the
return value.

```c filename=fill3_memory.c
int32 fill3_memory(int32* p) {
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
verifying "fill3_memory.c";

int32 fill3_memory(int32* p) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures first: p[0] == 0 by auto;
    ensures second: p[1] == 1 by auto;
    ensures third: p[2] == 2 by auto;
}
```

```expect
pass
```
