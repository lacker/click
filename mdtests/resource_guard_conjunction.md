# A resource body guarded by a conjunction

A resource body may be guarded by more than one condition. The guard then
lowers to a conjunction rather than to a bare condition, so deciding it is not
a job for the condition checker: the exact fact index answers it from the
requirements the caller stated.

Package 10(b) of `issues/simplify-kernel.md` dropped the general-prover leg
from `evaluate_guarded_contract_condition`, leaving the exact fact index, the
frozen condition checker on a bare condition, and the frozen atomic
memory/resource checkers. The census found no fixture whose guard was
anything but a bare condition, so this is the one that reaches the
structured-proposition leg; denying that leg rejects the `unfold` below.

```c filename=guard_conjunction.c
int32 read_both(int32* p, int32* q) {
    return *p;
}
```

```click
verifying "guard_conjunction.c";

resource pair(p: int32*, q: int32*) {
    if p != 0 and q != 0 {
        owns p[0..1];
    }
}

int32 read_both(int32* p, int32* q) {
    requires p != 0;
    requires q != 0;
    owns pair(p, q);
} by {
    unfold(pair(p, q));
    execute();
    simp();
}
```

```expect
pass
```
