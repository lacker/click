# The grouped `arithmetic() using` closer cites exactly its premises

`result <= 101` needs both caller bounds: without `n <= 100` the step is a
prompt, local arithmetic failure on the focused claim, not an ambient search
that finds the missing bound anyway.

```c filename=c_grouped_arithmetic_missing_premise.c
int32 bump(int32 n) { return n + 1; }
```

```click
verifying "c_grouped_arithmetic_missing_premise.c";

int32 bump(int32 n) {
    requires 0 <= n;
    requires n <= 100;
    ensures result <= 101;
} by {
    execute();
    arithmetic() using { 0 <= n; }
}
```

```expect
fail: `arithmetic` did not prove any current proposition goal
```
