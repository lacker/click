# A point a loop left on several paths names no state after it

This loop leaves at its test, when `take` finds `left` empty, and at its
`break`. Each leaving path recorded its own state at the test, so after the
loop `loop(0).test()` names no one state, and the read is refused naming the
two paths.

```c filename=two_exits.c
int take(int *n) {
    if (*n == 0) return 0;
    *n = *n - 1;
    return 1;
}
unsigned count(int n) {
    int left = n;
    unsigned c = 0;
    while (take(&left)) {
        if (c == 5) break;
        c = c + 1;
    }
    return c;
}
```

```click
verifying "two_exits.c";
int take(int *n) {
    requires *n >= 0;
    owns n[0..1];
    ensures result == (if old(*n) == 0 { 0 } else { 1 });
    ensures *n == (if old(*n) == 0 { 0 } else { old(*n) - 1 });
    ensures *n >= 0;
}
unsigned count(int n) {
    requires n >= 0;
    ensures true;
} by {
    step_until(loop(0).entry);
    loop {
        decreases 6 - to_integer(c);
        invariant c <= 5u32;
        invariant left >= 0;
    }
    have at(loop(0).test().entry, left) >= 0 by close();
}
```

```expect
fail: `loop(0)` left on 2 paths, and each recorded
```
