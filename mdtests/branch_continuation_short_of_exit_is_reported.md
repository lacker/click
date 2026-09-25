# A continuation that stops before the function exit is named

`clamp` returns early when `x` is negative, so the proof's `branch` has one
arm that returns and one that continues. The proof after the `branch` runs
inside the continuing arm, and here it stops before the function's second
`return`. The drivers decline such a proof, and the diagnostic used to call
the shape "not implemented in this execution context", which sends a reader
looking for an unsupported tactic. It now says the continuing arm's path was
left open, which is what the proof script has to fix.

```c filename=branch_continuation_short_of_exit.c
int32 clamp(int32 x) {
    if (x < 0) {
        return 0;
    }
    return x;
}
```

```click
verifying "branch_continuation_short_of_exit.c";

int32 clamp(int32 x) {
    ensures 0 <= result;
} by {
    branch {
        then {
            step();
            simp();
        }
        else {}
    }
}
```

```expect
fail: ran out before the continuing arm reached the function exit
```
