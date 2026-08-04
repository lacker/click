# a loop measure proves termination

```c filename=c_decreases_loop.c
int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "c_decreases_loop.c";

int32 drain(int32 n) {
    requires n >= 0;
    for loop(0) {
        decreases n;
        invariant n >= 0;
    }
    ensures result == 0 by auto;
}
```

```expect
pass
```
