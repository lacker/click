# a summarized loop inside a proof `if` arm

A proof-level `if` on the C condition is the other spelling for the same
guarded loop. Its arms never join: each one runs the function to its own exit,
so the arm that reaches the loop applies the rule and then continues through
the `return` on its own. The other arm skips the loop body entirely and needs
one more `step()` to reach the same `return`.

```c filename=loop_inside_a_proof_if_arm.c
int32 count_up(int32 n) {
    int32 i;
    i = 0;
    if (n > 0) {
        while (i < n) {
            i = i + 1;
        }
    }
    return i;
}
```

```click
verifying "loop_inside_a_proof_if_arm.c";

int32 count_up(int32 n) {
    ensures result >= 0;
} by {
    step();
    step();
    if n > 0 {
        step();
        loop {
            decreases n - i;
            invariant i >= 0;
            invariant i <= n;
        }
        step();
        simp();
    } else {
        step();
        step();
        step();
        simp();
    }
}
```

```expect
pass
```
