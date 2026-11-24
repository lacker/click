# `solve` closes an equality from opposite bounds at every width

`a == b` follows from `a <= b` and `b <= a`. At `int32` the order facts are
the kernel's signed order; at `uint32` they are the signed order of
sign-flipped operands, and at 64 bits their own orders, which the atomic
derivation does not combine into an equality. `solve` looks the two facts up
on the goal's operands, in any spelling (`a >= b`, `not (a < b)`), and closes
the goal with a `close() using` step citing them. A loop that counts to
its bound ends this way: its invariant gives `i <= n` and its exit `not (i <
n)`.

```c filename=widths.c
uint32_t pick32(uint32_t a, uint32_t b) {
    return a;
}

int64_t pick64(int64_t a, int64_t b) {
    return a;
}

uint64_t picku64(uint64_t a, uint64_t b) {
    return a;
}

uint32_t count(uint32_t n) {
    uint32_t i = 0;
    while (i < n) {
        i += 1;
    }
    return i;
}
```

```click
verifying "widths.c";

uint32 pick32(uint32 a, uint32 b) {
    requires a <= b;
    requires a >= b;
    ensures result == b;
}

int64 pick64(int64 a, int64 b) {
    requires b >= a;
    requires not (a < b);
    ensures result == b;
}

uint64 picku64(uint64 a, uint64 b) {
    requires a <= b;
    requires not (a < b);
    ensures result == b;
}

uint32 count(uint32 n) {
    ensures result == n;
} by {
    step_until(loop(0).entry);
    loop {
        decreases n - i;
        invariant i <= n;
        otherwise { have i == n by close(); }
    }
}
```

```expect
pass
```
