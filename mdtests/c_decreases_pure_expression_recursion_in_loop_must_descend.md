# a self-call inside a loop still owes the descent

The C is
[`c_decreases_pure_expression_recursion_in_loop.md`](c_decreases_pure_expression_recursion_in_loop.md)'s
with one edit: the recursive call passes `n` instead of the loop counter, so
the callee's measure is the caller's own entry measure and nothing descends.
The loop still ranks its own iterations, and `walk` still returns zero on
every path, so the only thing missing is the recursion's own back edge.

Being inside a summarized loop buys no leniency. The loop body is stepped
under `walk`'s recursion anchor, so the call raises the same member it raises
outside a loop, and the member stays open.

```c filename=c_decreases_pure_expression_recursion_in_loop_must_descend.c
int32 walk(int32 n) {
    int32 i;
    int32 result;
    i = 0;
    result = 0;
    while (i < n) {
        result = walk(n);
        i = i + 1;
    }
    return result;
}
```

```click
verifying "c_decreases_pure_expression_recursion_in_loop_must_descend.c";

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
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        invariant result == 0;
        initialize by simp;
        preserve by {
            have 0 <= level(n) by {
                unfold(level(n));
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
fail: `level(n)` decreases at the recursive call
```
