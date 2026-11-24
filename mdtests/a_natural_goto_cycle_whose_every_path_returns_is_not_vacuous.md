# a natural `goto` cycle whose every path returns is not vacuous

Every path of `maybe_stop` ends in the `return` inside the cycle. A loop rule
whose only path is `VerificationDiverges` would make any postcondition hold,
including this false one; the rule carries the return instead, and the
contract is refused on it.

```c filename=a_natural_goto_cycle_whose_every_path_returns_is_not_vacuous.c
int32 maybe_stop(int32 flag) {
again:
    if (flag == 0) {
        return 7;
    }
    flag = 0;
    goto again;
}
```

```click
verifying "a_natural_goto_cycle_whose_every_path_returns_is_not_vacuous.c";

int32 maybe_stop(int32 flag) {
    requires flag >= 0;
    ensures 1 == 0;
} by {
    loop {
        invariant flag >= 0;
        decreases flag;
    }
    close();
}
```

```expect
fail: 1 == 0
```
