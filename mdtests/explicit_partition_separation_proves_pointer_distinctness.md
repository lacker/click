# Explicit partition separation proves pointer distinctness

Pointer comparison does not discover separation by searching ownership
compositions or aliases. Name the separation, then use its indexed consequence.

```c filename=explicit_partition_separation_proves_pointer_distinctness.c
int distinct(int *p, int *q) { return p != q; }
```

```click
verifying "explicit_partition_separation_proves_pointer_distinctness.c";
int32 distinct(int32* p, int32* q) {
    owns *p;
    owns *q;
    ensures result == 1;
} by {
    have separate(memory(*p), memory(*q)) by { close(); }
    have p != q by { close(); }
    step();
}
```

```expect
pass
```
