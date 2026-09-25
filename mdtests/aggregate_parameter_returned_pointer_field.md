# An aggregate return does not extend a parameter's C lifetime

```c filename=aggregate_parameter_returned_pointer_field.c
struct packet { int32 value; };
struct output { int32* pointer; };
struct output leak(struct packet input) {
    struct output result;
    input.value = 7;
    result.pointer = &input.value;
    return result;
}
```

```click
verifying "aggregate_parameter_returned_pointer_field.c";
struct output leak(struct packet input) {
    ensures result.pointer[0] == 7;
} by { execute(); simp(); }
```

```expect
fail: checked outcome `simp` search did not retain a complete proof
```
