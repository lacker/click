# An unbounded `int64` sum still needs overflow evidence

Two `long` parameters carry no range from their type beyond `int64` itself,
so `a + b` may overflow. The width rule for widened 32-bit operands
([`int64_sum_of_widened_32_bit_operands.md`](int64_sum_of_widened_32_bit_operands.md))
does not apply to them, and with no `requires` bounds the signed-overflow
path remains reachable.

```c filename=int64_sum_without_bounds_overflows.c
long unbounded_sum(long a, long b) {
    return a + b;
}
```

```click
verifying "int64_sum_without_bounds_overflows.c";

int64 unbounded_sum(int64 a, int64 b) {
    ensures result == a + b;
} by {
    execute();
    simp();
}
```

```expect
fail: `step()` produced undefined behavior: signed overflow
```
