# `transport` reports an empty execution frontier

`transport(source, target)` reads the effects of completed execution steps.
At function entry there are none, so the tactic must say so instead of
reaching for an execution that does not exist yet.

```c filename=identity.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "identity.c";

int32 identity(int32 x) {
    requires x >= 0;

    ensures same: result == x by {
        transport(x >= 0, x >= 0);
        execute();
        simp();
    }
}
```

```expect
fail: `transport` requires a current statement frontier after at least one execution step
```
