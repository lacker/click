# UInt64 successor arithmetic

```click
import click::integer;

theorem false_successor_bound(length: uint64) {
    requires length < 18446744073709551615u64;
    requires length + 1u64 <= 9223372036854775807u64;
    ensures to_integer(length) + 1 <= 2147483647 by {
        have to_integer(length) < to_integer(18446744073709551615u64);
        have to_integer(length) + 1 <= 2147483647;
        close();
    }
}
```

```expect
fail: could not establish `(to_integer(length) + 1) <= 2147483647`
```
