# A summarized pure loop does not record its test state

Every loop has a test region. Applying a loop rule proves its exit without
stepping the individual passes, so it does not record a concrete state at
`loop(0).test().entry`. Reading that point requires stepping its test.

```c filename=pure_test.c
int drain(int n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "pure_test.c";
int drain(int n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
    }
    have at(loop(0).test().entry, n) == 0 by close();
}
```

```expect
fail: no symbolic state was recorded for `statement(0).test().entry`
```
