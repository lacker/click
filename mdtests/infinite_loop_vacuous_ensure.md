# A perpetual loop satisfies return postconditions vacuously

This deliberately surprising postcondition locks down partial-correctness
semantics. It does not prove that the function returns or that zero equals one.

```c filename=infinite_loop_vacuous_ensure.c
int32 spin_with_postcondition() {
    while (1) {
    }
    return 0;
}
```

```click
verifying "infinite_loop_vacuous_ensure.c";

int32 spin_with_postcondition() {
    for loop(0) {
        invariant 0 == 0;
    }

    ensures 0 == 1 by auto;
}
```

```expect
pass
```
