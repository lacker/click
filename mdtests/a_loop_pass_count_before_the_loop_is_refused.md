# A loop pass count before the loop is refused

A path that has not left a loop has no `loop(i).iterations` to read.

```c filename=iter.c
int32 doubled(int32 n) {
    int32 i;
    int32 total;
    i = 0;
    total = 0;
    while (i < n) {
        total = total + 2;
        i = i + 1;
    }
    return total;
}
```

```click
verifying "iter.c";

int32 doubled(int32 n) {
    requires n >= 0 and n <= 1000;
    ensures result == 2 * n;
} by {
    step();
    step();
    have loop(0).iterations == 0 by { close(); }
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant total == 2 * i;
    }
}
```

```expect
fail: unbound variable `loop(0).iterations`
```
