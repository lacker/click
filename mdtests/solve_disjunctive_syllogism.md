# solve proves one disjunct when the context refutes the other

`a == 0 or b < 5` and `a != 0` give `b < 5` by exact unit propagation.
The consequence is an ordinary available fact, so `solve` can close it with
`close()` without a case split. A Rust overflow check's pre-state requirement takes this
shape: `rhs == 0 or x <= 4294967295 / rhs` with `rhs != 0` known.

```c filename=solve_disjunctive_syllogism.c
void f(int32 a, int32 b) {}
```

```click
verifying "solve_disjunctive_syllogism.c";
void f(int32 a, int32 b) {
    requires a == 0 or b < 5;
    requires a != 0;
    ensures b < 5;
} by { have b < 5 by close(); step_until(function.exit); close(); }
```

```expect
pass
```
