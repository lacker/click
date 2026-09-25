# An `int64` guarded postcondition waits on an `int64` definedness step

This pins the `int64` frontier of
[`guarded_postcondition_closes_after_call.md`](guarded_postcondition_closes_after_call.md).
`bump` promises `st.total == old(st.total) + result` over `int64`, so after
the call the caller holds `defined(old(st.total) + got) implies st.total ==
old(st.total) + got`. Under `result == 1` the operands are bounded
(`old(st.total) < 100`, `got == 1`) and the sum cannot overflow; the smart
closer selects the guarded equality and spells its guard, but cannot prove
it.

The reduced cause is independent of calls: `have defined(a + b) by { simp(); }`
fails for `int64` operands with `a < 100` and `b == 1`, and so does
`simp() using { a < 100; b == 1; }`. Execution decides the same `int64`
overflow condition from the operands' intervals, but that decision has no
checkable simplifier evidence (there is no `int64` counterpart of the `int32`
arithmetic certificate), so no explicit step can state it. When that step
exists this file should pass unchanged.

```c filename=guarded_postcondition_int64_bounds_frontier.c
struct box {
    int v;
};

long bump(struct box* b) {
    return 1;
}

long caller(struct box* b) {
    long got;
    got = bump(b);
    return got;
}
```

```click
resource counted(b: struct box*) {
    field total: int64;
    owns object(b);
}

verifying "guarded_postcondition_int64_bounds_frontier.c";

int64 bump(struct box* b) {
    owns st: counted(b);
    requires st.total < 100;
    ensures result == 1 or result == 2;
    ensures st.total == old(st.total) + result;
} by {
    let { total: n } = unfold(st);
    let st = fold(counted(b), { total: n + 1 });
    execute();
    simp();
}

int64 caller(struct box* b) {
    owns st: counted(b);
    requires st.total < 100;
    ensures result == 1 implies st.total == old(st.total) + 1;
} by {
    step();
    step(bump(b), { st: st });
    execute();
    simp();
}
```

```expect
fail: `ensures (result == 1 => st.total == (old(st.total) + 1))` failed for `caller.ensures_1`
```
