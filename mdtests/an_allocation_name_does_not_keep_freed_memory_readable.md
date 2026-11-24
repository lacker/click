# An allocation name does not keep freed memory readable

Naming the fresh heap identity after `free` does not make the object live or
restore permission for an executed C read.

```c filename=allocation.c
int32 use_allocation() {
    int32* p;
    p = malloc(4);
    if (p == 0) return 0;
    free(p);
    return *p;
}
```

```click
verifying "allocation.c";
int32 use_allocation() { ensures true; } by {
    step();
    step();
    have statement(1).result == p by close();
    branch { true => { step(); } false => {} }
    have statement(1).allocation == p;
    have statement(1).allocation != 0;
    step();
    have statement(1).allocation != 0 by close();
    step();
}
```

```expect
fail: invalid memory access
```
