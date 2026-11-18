# An owned string keeps its value parameter's length

`keep` owns its string at a value parameter, `let m: uint64;` and
`owns cstr_at(p, m);`. An `owns` clause returns the instance it received, so
`old(m)` and the length at exit are the same value. The body is proved for
every length. `measure` supplies the length of its owned string in the
call map. The viewing form is
[`cstr_at_value_parameter_is_proved_for_every_length.md`](cstr_at_value_parameter_is_proved_for_every_length.md).

```c filename=cstr_at_owned_value_parameter_keeps_its_length.c
uint64 keep(uint8 *p, uint64 n)
{
	return n;
}

uint64 measure(uint8 *src, uint64 m)
{
	return keep(src, m);
}
```

```click
import click::c::string;

verifying "cstr_at_owned_value_parameter_keeps_its_length.c";

uint64 keep(uint8* p, uint64 n) {
    let m: uint64;
    owns cstr_at(p, m);
    requires n == m;
    ensures result == old(m);
}

uint64 measure(uint8* src, uint64 m) {
    owns cstr_at(src, m);
    ensures result == m;
} by {
    step(keep, { m: m });
}
```

```expect
pass
```
