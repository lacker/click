# A pure nested smart proof reports its own checked failure

Nested `have` bodies now run on `Proof`, including smart tactics. This
pointer-disequality symmetry search remains unsupported by the current
planner. The diagnostic identifies the failing `simp` in the `have` body,
without rerunning the source through the old certificate-only interpreter.
The original C and theorem remain the regression.

```c filename=symmetry.c
int nothing(void) { return 0; }
```

```click
verifying "symmetry.c";

theorem pointer_disequality_symmetry(a: int32*, b: int32*) {
    requires a != b;

    ensures 1 == 1 by {
        have b != a by { simp(); }
        normalize();
    }
}

int nothing() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: proof tactic 1 > have body tactic 1: `simp` failed
```
