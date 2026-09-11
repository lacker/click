# A lowering guard in front of a written implication

Lowering a quantified body folds the path facts it established into kernel
implications that no Surface connective wrote. Here `k + 1` may overflow for
an unconstrained `k`, so the lowered goal is

```text
forall k. (k + 1 does not overflow) implies ((k + 1 > 0 and k >= 0) implies k >= 0)
```

`intro` must reach that definedness guard without consuming the written
`implies`: the first introduction binds `k`, the second introduces the guard
while the written goal stays focused, and only the third introduces the
written antecedent. A proof that stops one introduction short still faces the
written implication.

```click
theorem guarded_universal() {
    ensures forall (k: int32) {
        k + 1 > 0 and k >= 0 implies k >= 0
    } by {
        intro();
        intro();
        intro();
        extract(k >= 0);
        assumption();
    }
}
```

```expect
pass
```
