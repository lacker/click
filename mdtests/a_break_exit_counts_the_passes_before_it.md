# A break exit counts the passes before it

A `break` leaves during a pass that does not count: the exit's count is the passes completed before it.

```c filename=brk.c
int32 count_up(int32 n) {
    int32 i;
    i = 0;
    while (1) {
        if (i >= n) {
            break;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "brk.c";

int32 count_up(int32 n) {
    requires n >= 0 and n <= 1000;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant i == iterations;
    }
    have loop(0).iterations == to_integer(n) by { close(); }
}
```

```expect
pass
```
