# multi-field struct fields

This checks that compact multi-field struct lowering still works with an
explicit object-range footprint. Most field-sized contracts should prefer
`read(p->field)` and `write(p->field)`.

```c filename=write_second.c
struct pair {
    int32 first;
    int32 second;
};

int32 write_second(struct pair* p) {
    p->first = 1;
    p->second = 2;
    return p->second;
}
```

```click
verifying "write_second.c";

int32 write_second(struct pair* p) {
    requires loadable(p[0..2]);
    consumes p[0..2];

    ensures result == 2 by auto;
    produces p[0..2] by auto;
}
```

```expect
pass
```
