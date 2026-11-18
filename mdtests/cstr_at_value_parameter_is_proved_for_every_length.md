# A function with a value parameter is proved for every value

`known_length`'s contract declares the string's length as a value parameter,
`let k: uint64;`, so its body is proved at an arbitrary `k`: the requirement
`n == k` and the postcondition both name it, and the proof never fixes it.
The caller supplies the held string's length in the call map. The owning form is
[`cstr_at_owned_value_parameter_keeps_its_length.md`](cstr_at_owned_value_parameter_keeps_its_length.md).

```c filename=cstr_at_value_parameter_is_proved_for_every_length.c
uint64 known_length(const uint8 *s, uint64 n)
{
	return n;
}

uint64 measure(const uint8 *src, uint64 m)
{
	return known_length(src, m);
}
```

```click
import click::c::string;

verifying "cstr_at_value_parameter_is_proved_for_every_length.c";

uint64 known_length(const uint8* s, uint64 n) {
    let k: uint64;
    views cstr_at(s, k);
    requires n == k;
    ensures result == k;
}

uint64 measure(const uint8* src, uint64 m) {
    views cstr_at(src, m);
    ensures result == m;
} by {
    step(known_length, { k: m });
}
```

```expect
pass
```
