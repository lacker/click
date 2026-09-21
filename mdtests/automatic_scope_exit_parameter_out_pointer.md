# A parameter's address expires on return

```c filename=parameter_out_pointer.c
void leak(int32 value, int32** out) { out[0] = &value; }
```

```click
verifying "parameter_out_pointer.c";
void leak(int32 value, int32** out) {
    consumes out[0..1];
    produces out[0..1];
    ensures *out[0] == value;
} by { execute(); simp(); }
```

```expect
fail: the proposition reads memory that is not viewable here
```
