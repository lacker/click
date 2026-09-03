# composite resource fold rejects a captured body fact

The resource parameter `n` is instantiated with the function parameter `i`,
while the body fact also binds `i`. A fold must not turn the free resource
argument into the inner binder and thereby certify the false fact `i >= i`.

```c filename=composite_resource_fold_rejects_captured_fact.c
int32 make(int32* p, int32 i) {
    return 0;
}
```

```click
resource bound(p: int32*, n: int32) {
    if p != 0 {
        owns p[0..1];
        fact forall (i: int32) {
            0 <= i and i < 3 implies n >= i
        };
    }
}

verifying "composite_resource_fold_rejects_captured_fact.c";

int32 make(int32* p, int32 i) {
    requires p != 0;
    consumes p[0..1];
    produces bound(p, i);
    ensures result == 0;
} by {
    execute();
    fold(bound(p, i));
    simp();
}
```

```expect
fail: requires an exact body fact
```
