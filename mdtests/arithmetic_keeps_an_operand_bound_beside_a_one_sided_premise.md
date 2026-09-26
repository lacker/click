# `arithmetic` keeps an operand bound beside a one-sided premise

A loop's back edge owes a stated range's extent bound over the new index
`i + 1`, and the loop head supplies both the invariant `0 <= i + 1` and, through
the guard, `i < n` with `n <= 1073741823`. The kernel spells the extent bound
with a sign-bit bias, `(-2147483648 ^ (i + 1)) <= -1073741825`, which the
signed-arithmetic certificate decides from an interval for `i + 1`.

The planner read that interval off the premise that bounds `i + 1` directly and
stopped there, so `0 <= i + 1` gave `i + 1` no upper bound and hid the one its
operands give (`i < n <= 1073741823`). Citing a true premise lost the
certificate: the same `arithmetic() using` without `0 <= i + 1` succeeded. A
one-sided direct bound is now intersected with the bound the operation's
operands give. The negative is
[`arithmetic_one_sided_premise_still_needs_the_operand_bound.md`](arithmetic_one_sided_premise_still_needs_the_operand_bound.md).

```c filename=arithmetic_keeps_an_operand_bound_beside_a_one_sided_premise.c
int32 next_index(int32 i, int32 n) {
    return i + 1;
}
```

```click
verifying "arithmetic_keeps_an_operand_bound_beside_a_one_sided_premise.c";

int32 next_index(int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    requires n <= 1073741823;
    ensures result == i + 1;
} by {
    have 0 <= i + 1 by {
        arithmetic() using { 0 <= i; i < n; n <= 1073741823; }
    }
    have (-2147483648 ^ (i + 1)) <= -1073741825 by {
        arithmetic() using {
            0 <= i + 1;
            0 <= i;
            i < n;
            n <= 1073741823;
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
