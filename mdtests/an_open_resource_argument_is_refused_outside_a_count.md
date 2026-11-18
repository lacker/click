# An open resource argument is refused outside a count pattern

`_` leaves a resource argument open only in a count pattern such as
`count(item(pool, _))`. An `owns` clause that leaves the length of the string
it owns open, `owns k: cstr_at(p, _);`, is refused; the contract declares the
length as a value parameter, `let n: uint64;`, and owns `cstr_at(p, n)`
([`cstr_at_owned_value_parameter_keeps_its_length.md`](cstr_at_owned_value_parameter_keeps_its_length.md)).

```c filename=an_open_resource_argument_is_refused_outside_a_count.c
unsigned long keep(unsigned char *p);
```

```click
import click::c::string;
verifying "an_open_resource_argument_is_refused_outside_a_count.c";

extern uint64 keep(uint8* p) {
    owns k: cstr_at(p, _);
    ensures result == k.len;
}
```

```expect
fail: `_` leaves a resource argument open only in a count pattern; declare the value as `let n: type;` and write `resource(..., n)`
```
