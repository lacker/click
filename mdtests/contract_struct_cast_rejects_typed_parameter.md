# A contract struct cast applies only to `void *` parameters

Casting a typed pointer parameter to another struct would let a contract read
a different object at the same address than the body can, so the parser
rejects it. Only an opaque `void *` parameter of the function under contract
may be cast.

```c filename=typed_cast.c
struct cell {
    int value;
};

int read_cell(int *p) {
    return p[0];
}
```

```click
verifying "typed_cast.c";

int32 read_cell(int32 *p) {
    views ((struct cell *)p)->value;
    ensures result == ((struct cell *)p)->value;
} by {
    execute();
    simp();
}
```

```expect
fail: a struct pointer cast applies to a `void *` parameter of the function under contract
```
