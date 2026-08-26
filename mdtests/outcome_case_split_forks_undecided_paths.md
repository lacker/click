# A post-execution case split forks the outcome paths it does not decide

After `execute()` the two return paths are `a` (when `a > 0`) and `0`.
The proof then splits on `a == 5`, which neither path decides. The checked
route forks each such path into two, one per polarity, records the case on
each copy, and certifies once per recorded case; each arm then closes the
postcondition on its copies.

```c filename=clamp_positive.c
int32 clamp_positive(int32 a) {
    if (a > 0) {
        return a;
    }
    return 0;
}
```

```click
verifying "clamp_positive.c";

int32 clamp_positive(int32 a) {
    ensures result >= 0;
} by {
    execute();
    if a == 5 {
        simp();
    } else {
        simp();
    }
}
```

```expect
pass
```
