# A local `char` array lends its C-string view to a call

`f` holds no resource for its local `tmp`: a local's bytes are implicit local
storage. A callee that views `cstr_at(s, n)` for a value parameter `n` takes
the view from those bytes, as it takes a plain view of a local. Every piece
of the string's body is lent from `tmp` as a checked local loan for the call,
and the string's facts are decided at the call from the bytes stored there.
The call map gives the length, since nothing the caller holds supplies it.
After each call the loan is closed, so `tmp[0] = 'a'` writes the array again,
and the second call views the same bytes twice.

```c filename=a_local_char_array_lends_its_c_string_view.c
unsigned long measure(const char *s);
unsigned long two(const char *s, const char *t);

unsigned long f(void)
{
	char tmp[12];
	unsigned long n;
	unsigned long m;

	tmp[0] = '\0';
	n = measure(tmp);
	tmp[0] = 'a';
	tmp[1] = '\0';
	m = two(tmp, tmp);
	return n + m;
}
```

```click
import click::c::string;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "a_local_char_array_lends_its_c_string_view.c";

extern uint64 measure(const char* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

extern uint64 two(const char* s, const char* t) {
    let na: uint64;
    views cstr_at(s, na);
    let nb: uint64;
    views cstr_at(t, nb);
    ensures result == na + nb;
}

uint64 f() {
    ensures result == 2u64;
} by {
    step();
    step();
    step();
    step();
    let { result: first } = step(measure, { n: 0u64 });
    step();
    step();
    step();
    let { result: second } = step(two, { na: 1u64, nb: 1u64 });
}
```

```expect
pass
```
