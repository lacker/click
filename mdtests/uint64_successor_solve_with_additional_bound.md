# UInt64 successor arithmetic

```click
import click::integer;

theorem successor_bound(length: uint64) {
    requires length < 18446744073709551615u64;
    requires length + 1u64 <= 9223372036854775807u64;
    ensures to_integer(length) + 1 <= 18446744073709551615 by {
        have to_integer(length) + 1 <= 18446744073709551615;
        close();
    }
}
```

```expect
pass
```
