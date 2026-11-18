# A call map gives a `let` value parameter its value

`measure` declares its string's length as a value parameter, `let n: uint64;`.
The caller holds no `cstr_at` instance for the local array `tmp`, so the call
cannot take `n` from one. The map names the value, `{ n: 0u64 }`, and the call
then requires `cstr_at(tmp, 0u64)`, which the caller assembles from the byte
`tmp[0] == 0`. `f` and `h` make the same call.

```c filename=step_value_map_gives_a_let_parameter_its_value.c
unsigned long measure(const char *s);

unsigned long f(void)
{
	char tmp[12];

	tmp[0] = '\0';
	return measure(tmp);
}

unsigned long h(void)
{
	char tmp[12];

	tmp[0] = '\0';
	return measure(tmp);
}
```

```click
import click::c::string;
verifying "step_value_map_gives_a_let_parameter_its_value.c";

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
    step(measure, { n: 0u64 });
}

uint64 h() {
    ensures result == 0u64;
} by {
    step();
    step();
    step(measure, { n: 0u64 });
}
```

```expect
pass
```
