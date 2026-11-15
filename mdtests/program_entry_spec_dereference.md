# Typed dereferences retain states

```c filename=main.c
unsigned int bump(unsigned int *p) { *p += 1; return *p; }
unsigned long bump64(unsigned long *p) { *p += 1; return *p; }
```

```click
verifying "main.c";
unsigned int bump(unsigned int *p) {
    owns *p;
    ensures to_integer(*p) == to_integer(old(*p) + 1u32);
    ensures *p == p[0];
    ensures old(*p) == old(p[0]);
}
unsigned long bump64(unsigned long *p) {
    owns *p;
    ensures to_integer(*p) == to_integer(old(*p) + 1u64);
    ensures *p == p[0];
    ensures old(*p) == old(p[0]);
}
```

```expect
pass
```
