# A loop's call writing a local struct forgets the struct's earlier value

`run` only views its parameter, so the loop's write set derived from the
function's resources is empty. The loop still writes `c`: each pass hands
`&c` to `bump`, which increments `c.n`. The loop head must therefore read
`c.n` afresh, not as the 0 stored before the loop, or the exit facts
(`c.n == i` and `i >= 3`) would contradict that 0 and prove any result.
`run` returns 3, so `ensures result == 7` is refused.

```c filename=loop_call_writes_local.c
struct counter { int32 n; };
void bump(struct counter *c);
int32 run(const int32 *p) {
    struct counter c;
    int32 i;
    c.n = 0;
    i = 0;
    while (i < 3) {
        bump(&c);
        i = i + 1;
    }
    return c.n;
}
```

```click
verifying "loop_call_writes_local.c";

extern void bump(struct counter *c) {
    owns c[0..1];
    requires c->n < 100;
    ensures c->n == old(c->n) + 1;
}

int32 run(const int32 *p) {
    views p[0..1];
    ensures result == 7;
} by {
    step_until(loop(0).entry);
    have c.n == 0;
    have separate(memory((&c as (uint8*))[0..4]), memory(p[0..1])) by { close(); }
    loop {
        decreases 3 - i;
        invariant 0 <= i and i <= 3;
        invariant c.n == i;
    }
}
```

```expect
fail: `ensures result == 7` failed
```
