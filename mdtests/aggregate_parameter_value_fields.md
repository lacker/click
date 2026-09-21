# Logical parameter fields preserve values without preserving C storage

```c filename=aggregate_parameter_value_fields.c
struct inner { int32 value; };
struct packet { struct inner inner; int32 items[2]; int32* data; };

int32 nested(struct packet input) { return input.inner.value; }
struct packet copy(struct packet input) { return input; }
```

```click
verifying "aggregate_parameter_value_fields.c";
int32 nested(struct packet input) {
    ensures result == input.inner.value;
} by { execute(); simp(); }
struct packet copy(struct packet input) {
    ensures result.inner.value == input.inner.value;
    ensures result.items[1] == input.items[1];
    ensures result.data == input.data;
} by { execute(); simp(); }
```

```expect
pass
```
