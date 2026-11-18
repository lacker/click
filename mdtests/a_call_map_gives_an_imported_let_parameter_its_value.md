# A call map gives an imported callee's `let` value parameter its value

`measure` is declared in an imported module with `let n: uint64;`. The
importing file's call map names `n` as the declaring file's would, in both
the callee form and the frontier form.

```c filename=a_call_map_gives_an_imported_let_parameter_its_value.c
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
import "a_call_map_gives_an_imported_let_parameter_its_value_module.click";
verifying "a_call_map_gives_an_imported_let_parameter_its_value.c";

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
