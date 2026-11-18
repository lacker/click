# A call step takes its arguments from the call at the frontier

A call step names its callee, `step(snprintf, { ... })`, not its call. The
format and arguments come from the call at the frontier, so the proof never
restates them. That matters here: the call passes
`(flags & 1) ? "" : " "`, which a proof expression cannot write.

The map gives the length of the `%s` of argument 0, value parameter `n0`,
the length of the string the local array `tmp` holds, `cstr_at(tmp, 0u64)`. The
`%s` of argument 1 takes the view of whichever string literal the condition
selects, so the call has one successor per value of `flags & 1`.

```c filename=step_value_map_takes_the_frontier_call.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int f(char *buf, int len, unsigned int flags)
{
	char tmp[12];

	tmp[0] = '\0';
	return snprintf(buf, len, "%s%s", tmp, (flags & 1) ? "" : " ");
}
```

```click
import click::c::string;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "step_value_map_takes_the_frontier_call.c";

int32 f(char buf[], int32 len, uint32 flags) {
    requires 9 <= len;
    owns buf[0..len as uint64];
    ensures result <= 1;
} by {
    have 0 <= len and len <= 2147483647 by solve();
    have to_integer(len as uint64) == to_integer(len) by {
        solve() using { 0 <= to_integer(len); to_integer(len) <= 2147483647; };
    }
    step();
    step();
    if (flags & 1u32) != 0u32 {
        step(snprintf, { n0: 0u64 });
        step_until(function.exit);
        solve();
    } else {
        let { result: count } = step(snprintf, { n0: 0u64 });
        step_until(function.exit);
        solve();
    }
}
```

```expect
pass
```
