# composite resource fold accepts a non-captured body fact

With a distinct body binder and the corresponding quantified precondition,
the same composite resource remains valid. This is the positive control for
the capture regression.

```c filename=composite_resource_fold_accepts_renamed_fact.c
int32 make(int32* p, int32 m) {
    return 0;
}
```

```click
resource bound(p: int32*, n: int32) {
    if p != 0 {
        owns p[0..1];
        fact forall (k: int32) {
            0 <= k and k < 3 implies n >= k
        };
    }
}

verifying "composite_resource_fold_accepts_renamed_fact.c";

int32 make(int32* p, int32 m) {
    requires p != 0;
    requires forall (k: int32) {
        0 <= k and k < 3 implies m >= k
    };
    consumes p[0..1];
    produces bound(p, m);
    ensures result == 0;
} by {
    execute();
    fold(bound(p, m));
    simp();
}
```

```expect
pass
```
