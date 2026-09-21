# Logical struct parameter values remain usable in contracts

```c filename=aggregate_parameter_logical_value.c
struct packet { int32 value; };
int32 read_value(struct packet input) { return input.value; }
```

```click
verifying "aggregate_parameter_logical_value.c";
int32 read_value(struct packet input) {
    ensures result == input.value;
} by { execute(); simp(); }
```

```expect
pass
```
