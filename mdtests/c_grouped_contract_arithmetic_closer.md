# A grouped contract proof closes a claim with `arithmetic() using`

A grouped `by { ... }` proof may close its claims with the explicit simple
arithmetic step instead of `simp()`: `arithmetic() using` names exactly the
premises the bound follows from, so the claim is discharged without search.

```c filename=c_grouped_contract_arithmetic_closer.c
int32 bump(int32 n) { return n + 1; }
```

```click
verifying "c_grouped_contract_arithmetic_closer.c";

int32 bump(int32 n) {
    requires 0 <= n;
    requires n <= 100;
    ensures result <= 101;
} by {
    execute();
    arithmetic() using { 0 <= n; n <= 100; }
}
```

```expect
pass
```
