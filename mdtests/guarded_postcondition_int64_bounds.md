# An `int64` guarded postcondition closes from its operands' bounds

This is the `int64` form of
[`guarded_postcondition_closes_after_call.md`](guarded_postcondition_closes_after_call.md).
`bump` promises `st.total == old(st.total) + result` over `int64`, so after
the call the caller holds `defined(old(st.total) + got) implies st.total ==
old(st.total) + got`. Under `result == 1` the operands are bounded
(`old(st.total) < 100`, `got == 1`), so the sum cannot overflow.

The smart closer selects the guarded equality and proves its guard with a
nested `simp`. For an `int64` sum that proof is the checked `int64_defined`
rule of the `special` arithmetic-certificate family: each operand's range is
its width range narrowed by the constant bounds the context indexes under
that operand, and the rule concludes definedness when the exact result range
stays inside `int64`. Expansion renders the discharge as

```text
have defined((old(st.total) + at(statement(2).exit, got))) by {
    arithmetic_certificate special {
        premise 0: old(st.total) < 100 => old(st.total) < 100;
        premise 1: at(statement(2).exit, got) == 1 => at(statement(2).exit, got) == 1;
        int64_defined bounds [0, 1] => defined((old(st.total) + at(statement(2).exit, got)));
        conclusion 0;
    }
}
```

followed by the `extract` and `rewrite` of the consequent, and the expansion
re-verifies (`src/surface/tests/expansion_tests.rs`). The explicit step on
its own, a widened operand, and the refusal when the bounds do not exclude
overflow are in [`int64_defined_from_bounds.md`](int64_defined_from_bounds.md)
and
[`int64_defined_bounds_do_not_exclude_overflow.md`](int64_defined_bounds_do_not_exclude_overflow.md).

```c filename=guarded_postcondition_int64_bounds.c
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

verifying "guarded_postcondition_int64_bounds.c";

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
pass
```
