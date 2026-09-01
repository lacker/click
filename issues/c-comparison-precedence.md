# Parse equality below relational precedence

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced with
`click verify` (exit 0) on a postcondition that the compiled function
contradicts.

`parse_compare` (`src/languages/c/syntax.rs:1496-1533`) folds all six
comparison operators into one left-associative precedence level above
`parse_shift`. C11 places `==` and `!=` strictly below `<`, `<=`, `>`, `>=`,
so `a == b < c` means `a == (b < c)`; Click builds `(a == b) < c`. Both trees
type-check because comparisons evaluate to int32 0 or 1
(`src/kernel/eval/expression.rs:169-234`), and the kernel faithfully evaluates
the wrong one. Divergence requires `==` or `!=` to the left of a relational
(`a == b < c`, `a != b > c`, `a < b == c < d`); chains with equality only on
the right parse the same either way. No test in `src/languages/c/tests.rs`
or `mdtests/` pins a mixed chain.

## Violated invariant

The trusted parser must build the expression tree C builds for every accepted
source.

## Intended regression

```c
int32 mixed(int32 a, int32 b, int32 c) { return a == b < c; }
```

```click
verifying "mixed.c";
int32 mixed(int32 a, int32 b, int32 c) {
    requires a == 5; requires b == 5; requires c == 9;
    ensures result == 1 by auto;
}
```

C computes `5 == (5 < 9)` which is `5 == 1`, so the function returns 0. Today
the sidecar verifies and `ensures result == 0` is rejected. After the fix the
sidecar must fail and `ensures result == 0` must verify.

## Acceptance criteria

- The parser has a separate equality level below the relational level, with
  left associativity within each level.
- A parser unit test asserts `a == b < c` lowers to
  `Equal(a, LessThan(b, c))` and `a < b == c < d` to
  `Equal(LessThan(a, b), LessThan(c, d))`.
- Negative and positive mdtests for the regression; `scripts/check.sh` passes.
