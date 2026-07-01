# theorem application in a function proof

This checks that a C function proof script can apply a pure theorem after
symbolic execution.

```c filename=theorem_apply_identity.c
int32 theorem_apply_identity(int32 x) {
    return x;
}
```

```click
verifying "theorem_apply_identity.c";

predicate nonnegative(int32 x) {
    x >= 0
}

theorem nonnegative_body(x: int32) {
    requires nonnegative(x);

    ensures x >= 0 by {
        unfold(nonnegative);
        simp();
    }
}

int32 theorem_apply_identity(int32 x) {
    requires nonnegative(x);

    ensures result >= 0 by {
        symbolic_execute();
        apply(nonnegative_body(result));
        simp();
    }
}
```

```expect
pass
```
