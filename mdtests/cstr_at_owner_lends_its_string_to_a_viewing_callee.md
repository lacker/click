# An owner lends its C string to a callee that views it

`measure` owns `cstr_at(src, n)` and calls `string_length`, whose contract
only views the string. The call lends the owned instance as a view for the
call's duration and returns ownership afterwards, without an unfold or a
refold.

```c filename=cstr_at_owner_lends_its_string_to_a_viewing_callee.c
uint64 string_length(const uint8 *s, uint64 n);

uint64 measure(uint8 *src, uint64 n)
{
	return string_length(src, n);
}
```

```click
import click::c::string;

verifying "cstr_at_owner_lends_its_string_to_a_viewing_callee.c";

extern uint64 string_length(const uint8* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(uint8* src, uint64 n) {
    owns cstr_at(src, n);
    ensures result == n;
}
```

```expect
pass
```
