# A call map value still requires the clause at that value

The map chooses `measure`'s `n`; it grants nothing. With `{ n: 1u64 }` the call
requires `cstr_at(tmp, 1u64)`, a string of length one, but `tmp[0]` is the
terminator, so the caller cannot assemble it and the call is refused.

```c filename=step_value_map_value_still_requires_its_clause.c
unsigned long measure(const char *s);

unsigned long f(void)
{
	char tmp[12];

	tmp[0] = '\0';
	return measure(tmp);
}
```

```click
import click::c::string;
verifying "step_value_map_value_still_requires_its_clause.c";

extern uint64 measure(const char* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 f() {
    ensures result == 1u64;
} by {
    step();
    step();
    step(measure, { n: 1u64 });
}
```

```expect
fail: assembling `views cstr_at(&tmp, 1u64)` from the caller's bytes requires an exact body fact
```
