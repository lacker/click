# `int64` definedness from the operands' bounds is an explicit step

`defined(a + b)` and `defined(a - b)` over `int64` lower to the negated
signed-overflow condition. The `int64_defined` node of the `special`
arithmetic-certificate family proves it: each operand starts from the width
range of its root constructor (a constant is itself, a value widened from
`unsigned int` lies in `[0, 2^32)`, one widened from `int` in
`[-2^31, 2^31)`, and any other `int64` term in the whole `int64` range), is
narrowed by the listed premises, and the rule holds when the exact sum or
difference of the two ranges stays inside `int64`. Each listed premise must be
a constant `int64` order or equality fact on one operand; the checker reads
only those premises.

`sum` and `difference` write the step out. `sum_by_simp` and
`sum_by_listed_simp` leave it to `simp` and `simp() using`, which cite the
constant bounds on each operand: the facts indexed under that operand, or the
listed ones. `mixed` adds an `int64` to a value widened from `unsigned int`:
only the `int64` operand needs a bound, and the postcondition states the exact
widened sum. A refusal when the bounds leave room for overflow is
[`int64_defined_bounds_do_not_exclude_overflow.md`](int64_defined_bounds_do_not_exclude_overflow.md).

```c filename=int64_defined_from_bounds.c
long sum(long a, long b) {
    return a + b;
}

long difference(long a, long b) {
    return a - b;
}

long sum_by_simp(long a, long b) {
    return a + b;
}

long sum_by_listed_simp(long a, long b) {
    return a + b;
}

long mixed(unsigned int tag, long b) {
    return tag + b;
}
```

```click
verifying "int64_defined_from_bounds.c";

int64 sum(int64 a, int64 b) {
    requires a < 100;
    requires b == 1;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        arithmetic_certificate special {
            premise 0: a < 100 => a < 100;
            premise 1: b == 1 => b == 1;
            int64_defined bounds [0, 1] => defined(a + b);
            conclusion 0;
        }
    }
    execute();
    simp();
}

int64 difference(int64 a, int64 b) {
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
            int64_defined bounds [0, 1, 2] => defined(a - b);
            conclusion 0;
        }
    }
    execute();
    simp();
}

int64 sum_by_simp(int64 a, int64 b) {
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

int64 sum_by_listed_simp(int64 a, int64 b) {
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

int64 mixed(uint32 tag, int64 b) {
    requires b < 100;
    ensures result == tag + b;
} by {
    have defined(tag + b) by {
        arithmetic_certificate special {
            premise 0: b < 100 => b < 100;
            int64_defined bounds [0] => defined(tag + b);
            conclusion 0;
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
