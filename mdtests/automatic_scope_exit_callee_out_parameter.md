# An out-parameter cannot extend a callee local lifetime

```c filename=leak.c
void leak(int32** out) { int32 a[1]; a[0] = 3; out[0] = &a[0]; }
```

```click
verifying "leak.c";
void leak(int32** out) {
    owns out[0..1];
    ensures *out[0] == 3;
} by { step_until(function.exit); close(); close(); }
```

```expect
fail: checked outcome `close` search did not retain a complete proof
```
