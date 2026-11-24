# `cases` after execution requires its disjunction

A `cases` after execution forks an outcome path only after proving that its alternatives cover that path. Here the contract gives `x == 1 or x == 3`, not the written `x == 1 or x == 2`, so the split is refused, naming the disjunction.

```c filename=cases_after_execution_requires_its_disjunction.c
int32 f(int32 x) {
    return x;
}
```

```click
verifying "cases_after_execution_requires_its_disjunction.c";

int32 f(int32 x) {
    requires x == 1 or x == 3;
    ensures result >= 1;
} by {
    step_until(function.exit);
    cases {
        x == 1 => { close(); }
        x == 2 => { close(); }
    }
}
```

```expect
fail: `cases` could not prove that its alternatives are exhaustive: `x == 1 or x == 2`
```
