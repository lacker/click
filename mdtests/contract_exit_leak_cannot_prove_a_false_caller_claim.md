# A leaked duplicate cell cannot prove a false caller claim

`leak` claims to return `wrap(p)` and `p[0..1]` from `wrap(p)` alone. If it
verified, `caller` would hold `p[0]` twice, `h(p, p)` would treat its two
owned cells as separate, and `caller` would prove `result == 2` although
`p[0]` is `1` when `h` returns. The duplicate return is refused at `leak`.

```c filename=leak.c
int32 leak(int32* p) {
    return 0;
}
int32 h(int32* a, int32* b) {
    b[0] = 2;
    a[0] = 1;
    return b[0];
}
int32 caller(int32* p) {
    leak(p);
    return h(p, p);
}
```

```click
resource wrap(p: int32*) {
    owns p[0..1];
}
verifying "leak.c";
int32 leak(int32* p) {
    owns wrap(p);
    produces p[0..1];
} by auto;
int32 h(int32* a, int32* b) {
    owns wrap(a);
    owns b[0..1];
    ensures result == 2;
} by {
    step();
    unfold(wrap(a));
    execute();
    fold(wrap(a));
    simp();
}
int32 caller(int32* p) {
    owns wrap(p);
    ensures result == 2;
} by auto;
```

```expect
fail: `leak.contract` path 0 left `leak.produces_0` unproved
```
