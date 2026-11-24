# Each arm of a split that ends a proof closes its own claims

A proof `if` after execution whose condition is open on the outcome path splits
that path in two, and each arm finishes its own path, closing that arm's
goals: here two `close()` steps close the first two claims in
each arm and the implicit closer the rest.

```c filename=solve_closes_each_arm_of_a_split_that_ends_a_proof.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "solve_closes_each_arm_of_a_split_that_ends_a_proof.c";

int32 f(int32 n) {
    ensures result == n;
    ensures n < 5 or n >= 5;
    ensures n == n;
} by {
    step_until(function.exit);
    if n < 5 {
        close();
        close();
    } else {
        close();
        close();
    }
}
```

```expect
pass
```
