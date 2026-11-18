# A wrong `snprintf` count is refused

`snprintf(buffer, 8, "%u", 42u)` returns 2; a claim that it returns 3 does not
follow from the format's contract.

```c filename=wrong_count.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int caller(char *buffer)
{
	return snprintf(buffer, 8, "%u", 42u);
}
```

```click
import click::c::stdio;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "wrong_count.c";

int32 caller(char buffer[]) {
    owns buffer[0..8];
    ensures result == 3 by {
        step_until(function.exit);
        have stdio::decimal_length(42u64) == 2u64 by {
            apply(stdio::decimal_length_2(42u64));
        }
        have result == 3 by {
            solve() using { result == stdio::decimal_length(42u64) as int32; stdio::decimal_length(42u64) == 2u64; };
        }
    }
}
```

```expect
fail: could not prove the current goal from only its listed premises
```
