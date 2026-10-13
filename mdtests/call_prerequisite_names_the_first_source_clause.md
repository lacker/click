# Missing call requirements retain source clause and tactic positions

The callee's name is first. The diagnostic must distinguish its name from
an ordinal, retain the original contract clause position, and count the
preceding have in the caller's written proof.

```c filename=pair.c
int32 first(int32 x, int32 y) { return x; }
int32 caller(int32 a, int32 b) { return first(a, b); }
```

```click
verifying "pair.c";
int32 first(int32 x, int32 y) {
    requires x > 0;
    requires y > 0;
    ensures 1 == 1 by auto;
}
int32 caller(int32 a, int32 b) {
    requires a <= 0;
    requires b > 0;
    ensures 1 == 1 by {
        have b > 0 or a > 0 by simp;
        step(); step(); simp();
    }
}
```

```expect
fail: tactic 1: `step()` is missing prerequisite (precondition clause 1 of `first`)
```
