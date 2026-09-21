# Explicit address-taking cannot read a retained logical parameter value

```c filename=aggregate_parameter_address_is_not_a_value.c
struct packet { int32 value; };
int32 read_value(struct packet input) { return input.value; }
```

```click
verifying "aggregate_parameter_address_is_not_a_value.c";
int32 read_value(struct packet input) {
    ensures result == *(&input.value);
} by { execute(); simp(); }
```

```expect
fail: unverified claims
```
