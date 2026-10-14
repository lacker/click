# simp proves one disjunct when the context refutes the other

`a == 0 or b < 5` and `a != 0` give `b < 5`. `simp` finds the disjunction
with the goal as one disjunct and every other disjunct refuted by an exact
fact, and eliminates it by `cases`, closing the refuted arm by
`contradiction`. A Rust overflow check's pre-state requirement takes this
shape: `rhs == 0 or x <= 4294967295 / rhs` with `rhs != 0` known.

```c filename=simp_disjunctive_syllogism.c
void f(int32 a, int32 b) {}
```

```click
verifying "simp_disjunctive_syllogism.c";
void f(int32 a, int32 b) {
    requires a == 0 or b < 5;
    requires a != 0;
    ensures b < 5;
} by { have b < 5 by simp; execute(); assumption(); }
```

```expect
pass
```
