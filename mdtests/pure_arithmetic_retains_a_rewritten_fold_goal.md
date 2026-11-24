# Arithmetic retains a rewritten fold goal

A `unfold` followed by explicit rewrites can leave a valid Integer goal
without a source template. Arithmetic must still emit a checked certificate.

```click
import click::integer;

function full_width_count(n: uint64) -> Integer {
    (0..n).fold(0, |acc, k| { acc + to_integer(1) })
}

theorem count_step(n: uint64) {
    requires 0u64 < n;
    requires full_width_count(n - 1u64) == to_integer(n - 1u64);
    ensures full_width_count(n) == to_integer(n) by {
        have 0u64 < n by close();
        have 1u64 <= n by close() using { 0u64 < n; };
        have to_integer(n - 1u64) < to_integer(n) by close() using { 0u64 < n; };
        have to_integer(0u64) <= to_integer(n - 1u64) by close();
        have to_integer(n - 1u64) < to_integer(18446744073709551615u64) by close() using { 0u64 < n; };
        unfold(full_width_count(n));
        rewrite(full_width_count(n - 1u64), to_integer(n - 1u64));
        have to_integer(1u64) <= to_integer(n);
        have to_integer(n - 1u64) == to_integer(n) - to_integer(1u64);
        rewrite(to_integer(n - 1u64), to_integer(n) - to_integer(1u64));
        close() using {};
    }
}
```

```expect
pass
```
