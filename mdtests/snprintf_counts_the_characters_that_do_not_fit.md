# `snprintf` counts the characters that do not fit

`snprintf(buf, 2, "%u", 123u)` writes `1` and a terminator, and returns 3,
the number of characters the format produces (C11 7.21.6.5p3). When the
output does not fit, the contract places the terminator in the buffer's last
byte. The proof states the nonzero size premise explicitly before using the
contract's guarded terminator guarantee.

```c filename=clipped.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int clipped(char *buf)
{
	return snprintf(buf, 2, "%u", 123u);
}
```

```click
import click::c::stdio;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "clipped.c";

int32 clipped(char buf[]) {
    owns buf[0..2];
    ensures result == 3 by {
        step_until(function.exit);
        have stdio::decimal_length(123u64) == 3u64 by {
            apply(stdio::decimal_length_3(123u64));
        }
        have result == 3 by {
            solve() using { result == stdio::decimal_length(123u64) as int32; stdio::decimal_length(123u64) == 3u64; };
        }
    }
    ensures buf[1] == 0 by {
        step_until(function.exit);
        have stdio::decimal_length(123u64) == 3u64 by {
            apply(stdio::decimal_length_3(123u64));
        }
        have stdio::decimal_length(123u64) >= 2u64 by {
            solve() using { stdio::decimal_length(123u64) == 3u64; };
        }
        have 2u64 != 0u64 by { normalize(); }
        solve();
    }
}
```

```expect
pass
```
