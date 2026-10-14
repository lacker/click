# an unsigned parameter measure must descend

This recursion swaps its arguments instead of reducing them, so `b` need not
shrink at the self-call. The descent member `a < b` is owed and nothing
establishes it.

```c filename=c_decreases_unsigned_parameter_recursion_swap.c
unsigned int gcd(unsigned int a, unsigned int b) {
    if (b == 0) {
        return a;
    }
    return gcd(b, a);
}
```

```click
verifying "c_decreases_unsigned_parameter_recursion_swap.c";

uint32 gcd(uint32 a, uint32 b) {
    decreases b;
    ensures result >= 0u32;
} by {
    execute();
    simp();
}
```

```expect
fail: `b` decreases at the recursive call
```
