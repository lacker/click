# An algebraic existential witness is not yet supported

The smallest missing proposition needed by the DFS reachability invariant is
an existential over `Nat`. This theorem does not involve C execution, arrays,
or loops: `Nat::Zero` is an immediate witness, but algebraic binders are
rejected before its proof can run.

```click
theorem nat_zero_exists() {
    ensures exists (fuel: Nat) { fuel == Nat::Zero } by {
        witness(fuel = Nat::Zero);
        normalize();
    }
}
```

```expect
fail: quantifier type must be a C type or Integer
```
