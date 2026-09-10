# An introduced antecedent is retained, not re-lowered

Introducing an implication adds its antecedent to the fact context, and that
changes what the same written antecedent lowers to. Here `n / k` is defined
only where `k` is not zero, so lowering the quantified body leaves two hidden
definedness guards in front of the written implication. Once the written
antecedent is introduced, the context says `k == 0`, and re-lowering
`n / k == n` under it keeps no path at all: the division's own guard is
refuted.

The introduction therefore retains the checked Surface-to-kernel antecedent
pair, and its structural conjuncts, at the moment it consumes the written
connective. `extract` cites one of those conjuncts and reads the retained
kernel fact instead of lowering the written form a second time.

The four introductions are the binder, the two definedness guards, and the
written antecedent, in that order.

```c filename=retained_antecedent_survives_its_introduction.c
int32 retained_antecedent(int32 n) {
    return n;
}
```

```click
verifying "retained_antecedent_survives_its_introduction.c";

int32 retained_antecedent(int32 n) {
    ensures result == n;
} by {
    step();
    have forall (k: int32) { k == 0 and n / k == n implies n == n } by {
        intro();
        intro();
        intro();
        intro();
        extract(n / k == n);
        normalize();
    }
    simp();
}
```

```expect
pass
```
