# Typed dereferences retain snapshots

```c filename=main.c
unsigned int bump(unsigned int *p) { *p += 1; return *p; }
unsigned long bump64(unsigned long *p) { *p += 1; return *p; }
```

```click
verifying "main.c";
unsigned int bump(unsigned int *p) {
    requires loadable(p[0..1]);
    consumes p[0..1]; produces p[0..1];
    ensures *p == old(*p) + 1u32;
    ensures *p == p[0];
    ensures old(*p) == old(p[0]);
} by { execute(); simp(); }
unsigned long bump64(unsigned long *p) {
    requires loadable(p[0..1]);
    consumes p[0..1]; produces p[0..1];
    ensures *p == old(*p) + 1u64;
    ensures *p == p[0];
    ensures old(*p) == old(p[0]);
} by { execute(); simp(); }
```

```expect
pass
```
