# A specification conditional is decided by the proof, not by lowering

Lowering a specification `if` reads no ambient fact. It folds only a
literally constant condition; every other condition lowers both branches, so
`select_when_positive`'s postcondition still mentions the conditional even
though `requires limit > 0` settles which branch applies. Choosing the branch
is a proof step.

```c filename=select_when_positive.c
int32 select_when_positive(int32 limit, int32 left, int32 right) {
    return left;
}
```

```click
verifying "select_when_positive.c";

int32 select_when_positive(int32 limit, int32 left, int32 right) {
    requires limit > 0;
    ensures result == (if limit > 0 { left } else { right });
} by auto;
```

```expect
pass
```
