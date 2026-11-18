# An `snprintf` call map gives the length of the C string a `%s` copies

A `%s` argument is viewed as `click::c::string::cstr_at(aN, nN)` for a value
parameter `nN`, so its length must come from somewhere. For a local array,
such as `tmp` here, nothing the caller holds supplies it. The call step gives
it: `step(snprintf, { n1: 0u64 })`. The format comes from the call at the
frontier and picks the formatted-output function. The length of the `%s` that converts argument `N`, counting from zero, is `nN`.
The string `cstr_at(tmp, 0u64)` is checked at the call, from `tmp`'s bytes.

`buf` is owned as `buf[0..len as uint64]`, the range the contract's `size`
names.

```c filename=snprintf_call_map_names_a_local_c_string.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int f(char *buf, int len)
{
	char tmp[12];

	tmp[0] = '\0';
	return snprintf(buf, len, "%u%s", (unsigned int)7, tmp);
}
```

```click
import click::c::string;
import click::format;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "snprintf_call_map_names_a_local_c_string.c";

int32 f(char buf[], int32 len) {
    requires 9 <= len;
    owns buf[0..len as uint64];
    ensures result == 1;
} by {
    have 0 <= len and len <= 2147483647 by solve();
    have to_integer(len as uint64) == to_integer(len) by {
        solve() using { 0 <= to_integer(len); to_integer(len) <= 2147483647; };
    }
    step();
    step();
    have format::decimal_length(7u64) == 1u64 by {
        apply(format::decimal_length_1(7u64));
    }
    step(snprintf, { n1: 0u64 });
    step();
    have result == format::decimal_length(7u64) as int32 by {
        solve();
    }
    have result == 1 by {
        solve() using { result == format::decimal_length(7u64) as int32; format::decimal_length(7u64) == 1u64; };
    }
}
```

```expect
pass
```
