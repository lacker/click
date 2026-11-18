# A named view is refused for a value parameter

A `views` clause is not named. A contract that needs the length of the
string it views declares it as a value parameter, `let n: uint64;`, and
writes `views cstr_at(s, n);`; the retired binder spelling
`views str: cstr_at(s, _);` is refused with that form as the repair.

```c filename=a_named_view_is_refused_for_a_value_parameter.c
unsigned long measure(const char *s);
```

```click
import click::c::string;
verifying "a_named_view_is_refused_for_a_value_parameter.c";

extern uint64 measure(const char* s) {
    views str: cstr_at(s, _);
    ensures result == str.len;
}
```

```expect
fail: a `views` clause is not named; declare each value it fixes as `let n: type;` and write `views resource(..., n);`
```
