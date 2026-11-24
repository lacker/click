# A parameter's address expires on return

```c filename=parameter_out_pointer.c
void leak(int32 value, int32** out) { out[0] = &value; }
```

```click
verifying "parameter_out_pointer.c";
void leak(int32 value, int32** out) {
    owns out[0..1];
    ensures *out[0] == value;
} by { step_until(function.exit); close(); close(); }
```

```expect
fail: checked outcome `close` search did not retain a complete proof
```
