# An unsigned measure that wraps upward is refused

The measure explicitly observes the machine subtraction with `to_integer`,
so its arithmetic still wraps in `uint32`. When `x` goes from 3 to 4, the measure goes
from 0 to 2^32 - 1. The test `x < 5u` still holds, so this edge owes descent.
An unwrapped `decreases 3 - x` would instead be an Integer difference.

```c filename=an_unsigned_measure_that_wraps_upward_is_refused.c
int32 fill(uint32 x) {
    while (x < 5u) {
        x++;
    }
    return 0;
}
```

```click
verifying "an_unsigned_measure_that_wraps_upward_is_refused.c";

int32 fill(uint32 x) {
    ensures result == 0;
} by {
    loop {
        decreases to_integer(3u32 - x);
        initialize by { close(); }
        maintain by {
            step();
        }
    }
}
```

```expect
fail: to_integer(3u32 - (at(statement(0).statement(0).entry, x) + 1u32)) < to_integer(3u32 - at(statement(0).statement(0).entry, x))
```
