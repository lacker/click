# `snprintf` states its result's sign and terminator through the result

The contract requires the number of characters the format produces to be at
most `INT_MAX`, and returns that number as `int`, so it also states that the
result is not negative and where the terminator is, read through the result:
at `buf[result as uint64]` when the output fits, and in the buffer's last byte
when it does not. A caller with a symbolic count, here the decimal length of
an arbitrary `unsigned` and of a C string it views, proves all three from the
call alone, without restating the count.

```c filename=never_negative.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int never_negative(char *buf, int len, unsigned int value, char *name)
{
	return snprintf(buf, len, "%u %s", value, name);
}
```

```click
import click::c::string;
import click::format;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "never_negative.c";

int32 never_negative(char buf[], int32 len, uint32 value, char name[]) {
    requires 1 <= len;
    requires to_integer(format::decimal_length(value as uint64)) + 8 <= 2147483646;
    views string::cstr_at(name, 8u64);
    owns buf[0..len as uint64];
    ensures 0 <= result;
    ensures result as uint64 < len as uint64 implies buf[result as uint64] == 0u8;
    ensures result as uint64 >= len as uint64 implies buf[len as uint64 - 1u64] == 0u8;
} by {
    have 0 <= len and len <= 2147483647 by solve();
    have to_integer(len as uint64) == to_integer(len) by {
        solve() using { 0 <= to_integer(len); to_integer(len) <= 2147483647; };
    }
    have len as uint64 != 0u64;
    step(snprintf, { n1: 8u64 });
}
```

```expect
pass
```
