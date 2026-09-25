# A by-value struct parameter's storage expires before postconditions

The field value may be retained as a logical contract value, but a pointer
exported to the parameter's C storage must not permit a post-return read.

```c filename=aggregate_parameter_dangling_out.c
struct packet { int32 value; };
void leak(struct packet input, int32** out) {
    input.value = 7;
    out[0] = &input.value;
}
```

```click
verifying "aggregate_parameter_dangling_out.c";
void leak(struct packet input, int32** out) {
    consumes out[0..1];
    produces out[0..1];
    ensures *out[0] == 7;
} by { execute(); simp(); }
```

```expect
fail: checked outcome `simp` search did not retain a complete proof
```
