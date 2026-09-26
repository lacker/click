# `int32` definedness from the operands' bounds is an explicit step

This is the `int32` form of
[`int64_defined_from_bounds.md`](int64_defined_from_bounds.md).
`defined(a + b)` and `defined(a - b)` over `int32` lower to the negated
signed-overflow condition. The `int32_defined` node of the `special`
arithmetic-certificate family proves it with the same checker as
`int64_defined`, parameterized by width: each operand starts from the width
range of its root constructor (a constant is itself; `char` and `short`
values share the unconverted 32-bit term, so any other `int32` term has the
whole `int32` range), is narrowed by the listed premises, and the rule holds
when the exact sum or difference of the two ranges stays inside `int32`. Each
listed premise must be a constant `int32` order or equality fact on one
operand; the checker reads only those premises.

`sum` and `difference` write the step out. `sum_by_simp`,
`difference_by_simp`, and `sum_by_listed_simp` leave it to `simp` and
`simp() using`, which cite the constant bounds on each operand: the facts
indexed under that operand, or the listed ones. `sum_by_arithmetic` cites the
listed ones through `arithmetic() using`.

`bump` and `caller` are the `int32` form of
[`guarded_postcondition_int64_bounds.md`](guarded_postcondition_int64_bounds.md):
after the call the caller holds `defined(old(st.total) + got) implies
st.total == old(st.total) + got`, and under `result == 1` the operands are
bounded (`old(st.total) < 100`, `got == 1`). The smart closer proves the guard
with a nested `simp`, whose certificate is the checked `int32_defined` rule
citing those two constant bounds; the expansion of `caller` re-verifies
(`src/surface/tests/expansion_tests.rs`).

The refusals are
[`int32_defined_bounds_do_not_exclude_overflow.md`](int32_defined_bounds_do_not_exclude_overflow.md)
(both operands bounded, but not enough),
[`int32_defined_one_operand_bounded.md`](int32_defined_one_operand_bounded.md)
(the other operand keeps its whole `int32` range), and
[`int32_defined_unrelated_bound.md`](int32_defined_unrelated_bound.md)
(a listed premise that bounds no operand).

```c filename=int32_defined_from_bounds.c
struct box {
    int v;
};

int sum(int a, int b) {
    return a + b;
}

int difference(int a, int b) {
    return a - b;
}

int sum_by_simp(int a, int b) {
    return a + b;
}

int difference_by_simp(int a, int b) {
    return a - b;
}

int sum_by_listed_simp(int a, int b) {
    return a + b;
}

int sum_by_arithmetic(int a, int b) {
    return a + b;
}

int bump(struct box* b) {
    return 1;
}

int caller(struct box* b) {
    int got;
    got = bump(b);
    return got;
}
```

```click
resource counted(b: struct box*) {
    field total: int32;
    owns object(b);
}

verifying "int32_defined_from_bounds.c";

int32 sum(int32 a, int32 b) {
    requires a < 100;
    requires b == 1;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        arithmetic_certificate special {
            premise 0: a < 100 => a < 100;
            premise 1: b == 1 => b == 1;
            int32_defined bounds [0, 1] => defined(a + b);
            conclusion 0;
        }
    }
    execute();
    simp();
}

int32 difference(int32 a, int32 b) {
    requires -5 <= a;
    requires 0 <= b;
    requires not (b > 7);
    ensures result == a - b;
} by {
    have defined(a - b) by {
        arithmetic_certificate special {
            premise 0: -5 <= a => -5 <= a;
            premise 1: 0 <= b => 0 <= b;
            premise 2: not (b > 7) => not (b > 7);
            int32_defined bounds [0, 1, 2] => defined(a - b);
            conclusion 0;
        }
    }
    execute();
    simp();
}

int32 sum_by_simp(int32 a, int32 b) {
    requires a < 100;
    requires b == 1;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        simp();
    }
    execute();
    simp();
}

int32 difference_by_simp(int32 a, int32 b) {
    requires -5 <= a;
    requires 0 <= b;
    requires not (b > 7);
    ensures result == a - b;
} by {
    have defined(a - b) by {
        simp();
    }
    execute();
    simp();
}

int32 sum_by_listed_simp(int32 a, int32 b) {
    requires a < 100;
    requires b == 1;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        simp() using {
            a < 100;
            b == 1;
        }
    }
    execute();
    simp();
}

int32 sum_by_arithmetic(int32 a, int32 b) {
    requires a < 100;
    requires b == 1;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        arithmetic() using {
            a < 100;
            b == 1;
        }
    }
    execute();
    simp();
}

int32 bump(struct box* b) {
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

int32 caller(struct box* b) {
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
