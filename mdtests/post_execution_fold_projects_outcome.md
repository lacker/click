# post-execution fold projects the outcome working set

A `fold(...)` after execution has reached function exit defers through
ordered finalization into the drain's resource-projection arm, which
rewrites the per-path working set and must re-import it into the typed
outcome goal immediately. This is the regression for that projection arm
(`issues/drain-legacy-arms-uncovered.md`).

```c filename=seal.c
int32 seal(int32 x) {
    return x;
}
```

```click
abstract resource permit(x: int32);

resource bundle(x: int32) {
    contains permit(x);
}

verifying "seal.c";

int32 seal(int32 x) {
    consumes permit(x);
    produces bundle(x);
    ensures result_matches: result == x;
} by {
    execute();
    fold(bundle(x));
    simp();
}
```

```expect
pass
```
