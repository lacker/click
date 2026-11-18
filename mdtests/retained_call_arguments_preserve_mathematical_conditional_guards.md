# Retained call arguments preserve mathematical conditional guards

```click
import click::c::stdio;

theorem retained_guard(v: uint64, width: uint64, k: uint64) {
    ensures 48u8 <= stdio::padded_digit(v, width, 48u8, k) by {
        unfold(stdio::padded_digit(v, width, 48u8, k));
        if to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)) {
            normalize() using { to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)); };
        } else {
            apply(stdio::decimal_digit_lower_bound(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v))));
            solve() using { not (to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v))); 48u8 <= stdio::decimal_digit(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v))); };
        }
    }
}
```

```expect
pass
```
