# A language-named program binding is refused

A program binding a Click name shadows is written `program::name` in every
source language. The earlier forms `c(name)` and `rust(name)` are refused,
and the refusal names the replacement.

```c filename=named.c
int32 count(int32 n) {
    int32 iterations;
    iterations = 0;
    while (iterations < n) {
        iterations = iterations + 1;
    }
    return iterations;
}
```

```click
verifying "named.c";

int32 count(int32 n) {
    requires n >= 0 and n <= 1000;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - program::iterations;
        invariant 0 <= program::iterations and program::iterations <= n;
        invariant c(iterations) == iterations;
    }
    have loop(0).iterations == n by { close(); }
}
```

```expect
fail: `c(iterations)` is no longer Click syntax: a program binding is `program::iterations`
```
