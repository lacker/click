# a recursion measure over a variable the loop havocs

The loop assigns `n`, which is the variable the recursion measure reads, so
the body's proof runs from an iteration state where `n` is an arbitrary value
the invariants constrain. The measure the descent is compared against is not
that value: the kernel read `level(n)` once, at `walk`'s entry, and the term
it produced names the entry symbol, which no havoc can rebind — the
environment reserves the anchor's variables, so no fresh iteration value is
handed out on top of one.

A loop phase proof reads `old(...)` at the function entry, the same state the
anchor read, so `level(old(n))` is the entry measure spelled in the proof.
What relates the iteration's `n` to it is `invariant n <= old(n)`, a fact only
the user's loop clauses can carry.

```c filename=c_decreases_pure_expression_recursion_in_havocked_loop.c
int32 walk(int32 n) {
    int32 result;
    result = 0;
    while (n > 0) {
        result = walk(n - 1);
        n = n - 1;
    }
    return result;
}
```

```click
verifying "c_decreases_pure_expression_recursion_in_havocked_loop.c";

function level(n: int32) -> int32 {
    n
}

int32 walk(int32 n) {
    decreases level(n);
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases n;
        invariant n >= 0;
        invariant n <= old(n);
        invariant result == 0;
        initialize by simp;
        preserve by {
            have 0 <= level(n - 1) by {
                unfold(level(n - 1));
                simp();
            }
            have level(n - 1) < level(old(n)) by {
                unfold(level(n - 1));
                unfold(level(old(n)));
                apply(int32_positive_predecessor_strictly_decreases(n)) using {
                    n > 0;
                }
                simp();
            }
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
