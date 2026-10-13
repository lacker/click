# A decremented argument keeps only its shifted upper bound

`n <= 100` bounds `n - 1` by `99`, not by `98`: at `n = 100` the callee's
`x <= 98` is false, so the call's precondition is refused even though the
shifted-bound rule proves `n - 1 <= 99`.

```c filename=call_precondition_refuses_a_decremented_upper_bound_too_tight.c
int32 id(int32 x) {
    return x;
}

int32 caller(int32 n) {
    return id(n - 1);
}
```

```click
verifying "call_precondition_refuses_a_decremented_upper_bound_too_tight.c";

int32 id(int32 x) {
    requires x <= 98;
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller(int32 n) {
    requires n <= 100;
    requires 0 < n;
    ensures result == n - 1;
} by {
    execute();
    simp();
}
```

```expect
fail: did not derive `n - 1 <= 98`
```
