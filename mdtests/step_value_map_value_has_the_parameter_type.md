# A call map value has its parameter's type

`measure`'s `n` is a `uint64`; the entry `{ n: 0u32 }` gives it a `uint32`
and the call is refused, naming both types. Write the value at the
parameter's type, `0u64`.

```c filename=step_value_map_value_has_the_parameter_type.c
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
verifying "step_value_map_value_has_the_parameter_type.c";

extern uint64 measure(const char* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 f() {
    ensures result == 0u64;
} by {
    step();
    step();
    step(measure, { n: 0u32 });
}
```

```expect
fail: the call map gives `n` a `uint32` value; it takes a `uint64`
```
