# Bounded `int64` arithmetic is defined

Order facts on `int64` values bound each operand of a 64-bit addition or
subtraction. When the bounds keep every result inside `int64`, the kernel
decides the signed-overflow condition false from those facts and execution
takes only the defined path. The bounds are looked up under the operand
terms themselves, never found by scanning the context.

The difference's bounds sit at the edge: `a - b` ranges exactly over
`[INT64_MIN, INT64_MAX]`. Without bounds the same operations still report
signed overflow
([`int64_sum_without_bounds_overflows.md`](int64_sum_without_bounds_overflows.md)).

```c filename=int64_sum_with_bounds.c
long bounded_sum(long a, long b) {
    return a + b;
}

long bounded_difference(long a, long b) {
    return a - b;
}
```

```click
verifying "int64_sum_with_bounds.c";

int64 bounded_sum(int64 a, int64 b) {
    requires 0 <= a;
    requires a <= 1000;
    requires -1000 <= b;
    requires b < 1000;
    ensures result == a + b;
} by {
    execute();
    simp();
}

int64 bounded_difference(int64 a, int64 b) {
    requires -4611686018427387904 <= a;
    requires a <= 4611686018427387903;
    requires -4611686018427387904 <= b;
    requires b <= 4611686018427387904;
    ensures result == a - b;
} by {
    execute();
    simp();
}
```

```expect
pass
```
