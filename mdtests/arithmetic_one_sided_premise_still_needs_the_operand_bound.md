# A one-sided premise still needs the operand bound it is paired with

The negative of
[`arithmetic_keeps_an_operand_bound_beside_a_one_sided_premise.md`](arithmetic_keeps_an_operand_bound_beside_a_one_sided_premise.md).
Here `n` may be one past the largest four-byte element count, so `i < n`
bounds `i + 1` only by `1073741824`, and for `i == 1073741823` the biased
extent bound `(-2147483648 ^ (i + 1)) <= -1073741825` is false. Intersecting
the direct `0 <= i + 1` with the operands' bound does not reach below the
limit, so the certificate is still refused.

```c filename=arithmetic_one_sided_premise_still_needs_the_operand_bound.c
int32 next_index(int32 i, int32 n) {
    return i + 1;
}
```

```click
verifying "arithmetic_one_sided_premise_still_needs_the_operand_bound.c";

int32 next_index(int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    requires n <= 1073741824;
    ensures result == i + 1;
} by {
    have 0 <= i + 1 by {
        arithmetic() using { 0 <= i; i < n; n <= 1073741824; }
    }
    have (-2147483648 ^ (i + 1)) <= -1073741825 by {
        arithmetic() using {
            0 <= i + 1;
            0 <= i;
            i < n;
            n <= 1073741824;
        }
    }
    execute();
    simp();
}
```

```expect
fail: (-2147483648 ^ (i + 1)) <= -1073741825
```
