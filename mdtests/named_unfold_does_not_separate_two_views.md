# An opened owner does not make two independent views disjoint

```c filename=probe.c
void check(int32* p, int32* q, int32* owned) {}
```

```click
resource owner(p: int32*) {
    field unused: int32;
    owns p[0..1];
}
verifying "probe.c";
void check(int32* p, int32* q, int32* owned) {
    views p[0..1];
    views q[0..1];
    consumes r: owner(owned);
} by {
    let { unused: m } = unfold(r);
    have separate(memory(p[0..1]), memory(q[0..1])) by { close(); }
    step_until(function.exit);
}
```

```expect
fail: could not establish `separate(memory(p[0..1]), memory(q[0..1]))`
```
