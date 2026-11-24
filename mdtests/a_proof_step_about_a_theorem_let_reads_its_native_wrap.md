# A proof step about a theorem `let` reads its native wrap

`let n: int8 = v + 1;` is the native `int8` sum, which wraps to `-128` at
`v == 127`, in the clause and in every step of its proof. The `have` below
claims the exact sum `to_integer(v) + 1`, which holds of C's promoted
`int32` sum but not of `n`, and is refused.

`a_theorem_let_names_its_native_operation_in_a_proof_step.md` proves the
bound the native sum does have.

```click quick-solve
theorem have_wraps(v: int8) {
    let n: int8 = v + 1;
    ensures to_integer(n) <= 127 by {
        have to_integer(n) == to_integer(v) + 1 by { close(); }
    }
}
```

```expect
fail: could not establish `to_integer(n) == (to_integer(v) + 1)`
```
