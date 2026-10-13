# A recursive call cannot keep a lower bound its argument drops below

`requires 1 <= n` does not hold for `n - 1` at `n = 1`, the smallest `n`
that reaches the recursive call, so the call's precondition is refused.

The refusal lists the facts the check consulted. The call is checked over
the proof context, which holds the contract's requirements and the branch's
`n <= 0` refutation; the refusal used to report "0 ambient condition facts"
because it listed only the statement's own new facts.

```c filename=recursive_call_precondition_refuses_a_decremented_lower_bound.c
int32 count(int32 n) {
    if (n <= 0) {
        return 0;
    }
    return count(n - 1);
}
```

```click
verifying "recursive_call_precondition_refuses_a_decremented_lower_bound.c";

int32 count(int32 n) {
    requires n <= 100;
    requires 1 <= n;
    decreases n;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: condition-certificate premise search did not derive `1 <= n - 1` from 4 ambient condition facts: [1 <= n, n > 0, n <= 100
```
