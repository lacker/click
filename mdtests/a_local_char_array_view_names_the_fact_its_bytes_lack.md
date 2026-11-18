# A local array's C-string view names the fact its bytes lack

`tmp[0]` is the terminator, so `tmp` holds `cstr_at(tmp, 0u64)` and no
longer string. A call map that gives the length `1u64`, so that the call
requires `cstr_at(tmp, 1u64)`, is refused at the
body fact the bytes do not establish, that the byte before the terminator is
nonzero, rather than as a missing loan.

```c filename=a_local_char_array_view_names_the_fact_its_bytes_lack.c
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
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "a_local_char_array_view_names_the_fact_its_bytes_lack.c";

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
    let { result: r } = step(measure, { n: 1u64 });
}
```

```expect
fail: assembling `views cstr_at(&tmp, 1u64)` from the caller's bytes requires an exact body fact: missing pure fact: `forall (k: uint64) { 0u64 <= k and k < len implies p[k] != 0u8 }` (with p = &tmp, len = 1u64)
```
