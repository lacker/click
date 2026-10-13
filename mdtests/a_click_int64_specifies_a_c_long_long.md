# A Click `int64` specifies a C `long long`

Click's `int64` and `uint64` name 64-bit representations, not C ranks, so a
specification written with them matches a C `long long` or `unsigned long
long` signature as well as a `long` one. The C declarations keep their own
compatibility rules.

```c filename=main.c
long long first(long long *p) {
    return p[0];
}

unsigned long long *same(unsigned long long *p) {
    return p;
}
```

```click
verifying "main.c";

int64 first(int64 *p) {
    views p[0];
    ensures result == p[0];
} by {
    execute();
    simp();
}

uint64 *same(uint64 *p) {
    ensures result == p by auto;
}
```

```expect
pass
```
