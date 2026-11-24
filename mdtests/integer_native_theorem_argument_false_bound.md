# A converted native argument cannot gain a false bound

```click
import click::integer;
theorem bounded(z: Integer) {
 requires z >= 0;
 requires z <= 18446744073709551615;
 requires z <= 65520;
 ensures to_uint64(z) <= 65519u64 by {
  have z <= 18446744073709551615 by close() using { z <= 65520; };
  apply(integer::to_uint64_round_trip(z));
  have to_integer(to_uint64(z)) <= to_integer(65519u64) by close() using { to_integer(to_uint64(z)) == z; z <= 65520; };
  close();
 }
}
```

```expect
fail: arithmetic
```
