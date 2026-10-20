# A signed loop certificate retains its native type

The loop rank is an Integer expression, while its counter bounds are native
int32 facts. Generated signed certificates must retain that native carrier
when reparsed under the file's Integer arithmetic default.

```c filename=signed_loop.c
int f(int n) {
    int i = 0;
    while (i < n) { i = i + 1; }
    return i;
}
```

```click
arithmetic "integer";
verifying "signed_loop.c";
int32 f(int32 n) {
    requires 0 <= n;
    requires n <= 100;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    execute();
    simp();
}
```

```expect
pass
```
