# A perpetual loop satisfies return postconditions vacuously

This deliberately surprising postcondition locks down partial-correctness
semantics. It does not prove that the function returns or that zero equals one.
The `diverges` marker is what says so out loud: the loop is meant never to
exit, and the `ensures` claims only what holds if the function returns.

```c filename=infinite_loop_vacuous_ensure.c
int32 spin_with_postcondition() {
    while (1) {
    }
    return 0;
}
```

```click
verifying "infinite_loop_vacuous_ensure.c";

int32 spin_with_postcondition() diverges {
    ensures 0 == 1;
} by {
    loop diverges {
        invariant 0 == 0;
    }
    simp();
}
```

```expect
pass
```
