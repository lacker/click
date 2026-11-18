# A call map names only value parameters the callee declares

`step(snprintf, { ... })` takes its format from the call at the frontier, so
its entries are checked against that call's contract when the step runs. This
`snprintf`'s only `%s` converts argument 1, so its one value parameter is
`n1`. An entry for `n0` is refused and names the call.

```c filename=step_value_map_names_a_parameter_the_callee_lacks.c
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
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "step_value_map_names_a_parameter_the_callee_lacks.c";

int32 f(char buf[], int32 len) {
    requires 9 <= len;
    owns buf[0..len as uint64];
    ensures result >= 0;
} by {
    step();
    step();
    step(snprintf, { n0: 0u64 });
}
```

```expect
fail: `snprintf` with format "%u%s" declares no value parameter `n0`
```
