# A step can cite the nonnegative operand of a signed word OR

```c filename=arithmetic.c
int32 divide(int32 n, int32 k) { return n / ((k & 7) | 1); }
```

```click
verifying "arithmetic.c";

int32 divide(int32 n, int32 k) { ensures true; } by {
    step() by {
        have (k & 7) >= 0 by { close(); }
        close();
    }
}

theorem sign(k: int32) {
    requires k >= 0;
    ensures (k | 1) != -1 by { close(); }
}
```

```expect
pass
```
