# A goal rewrite cannot skip an earlier claim

```c filename=rewrite_claim.c
int f(int x, int y, int z) { return x; }
```

```click
verifying "rewrite_claim.c";

int32 f(int32 x, int32 y, int32 z) {
    requires x == y;
    requires z == 0;
    ensures z == 0;
    ensures result == y;
} by {
    step_until(function.exit);
    rewrite(y, x);
    close();
    close();
}
```

```expect
fail: equality does not occur in the current goal
```
