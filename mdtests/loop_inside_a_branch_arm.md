# a summarized loop inside a `branch` arm

An ordinary C loop guarded by an `if` is reached only on one path, so the proof
splits the `if` with `branch` and writes the loop tactic in the arm that runs
it. The loop rule is applied at the arm's frontier with the arm's path
condition available, and the two arms join at the statement after the `if`
through the `ensuring` interface: the then arm leaves `i` at the loop's
abstract exit and the else arm leaves it at `0`, so the shared lower bound is
what the continuation gets.

```c filename=loop_inside_a_branch_arm.c
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
verifying "loop_inside_a_branch_arm.c";

int32 count_up(int32 n) {
    ensures result >= 0;
} by {
    step();
    step();
    branch {
        ensuring {
            fact i >= 0;
        }
        then {
            loop {
                decreases n - i;
                invariant i >= 0;
                invariant i <= n;
            }
        }
        else {}
    }
    step();
    simp();
}
```

```expect
pass
```
