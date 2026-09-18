# a pure recursion measure reaches a self-call inside a summarized loop

The recursive call sits in a loop, so it is taken by the loop's own judgment
rather than by a step of `walk`'s proof. The loop is certified under `walk`'s
recursion anchor all the same: the kernel installs it for every loop of the
function that declared the measure, so the call inside the body owes the two
members it would owe outside one, and against the same function-entry value
of `level(n)`.

The two termination arguments stay independent. `decreases n - i` ranks the
loop's own iterations; `decreases level(n)` ranks the recursion, and the facts
that discharge it come from the loop's clauses: `invariant 0 <= i` makes the
callee's measure nonnegative, and the guard `i < n` makes it strictly below
the entry value.

```c filename=c_decreases_pure_expression_recursion_in_loop.c
int32 walk(int32 n) {
    int32 i;
    int32 result;
    i = 0;
    result = 0;
    while (i < n) {
        result = walk(i);
        i = i + 1;
    }
    return result;
}
```

```click
verifying "c_decreases_pure_expression_recursion_in_loop.c";

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
            have 0 <= level(i) by {
                unfold(level(i));
                simp();
            }
            have level(i) < level(n) by {
                unfold(level(i));
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
pass
```
