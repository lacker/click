# An out-parameter cannot extend a callee local lifetime

```c filename=leak.c
void leak(int32** out) { int32 a[1]; a[0] = 3; out[0] = &a[0]; }
```

```click
verifying "leak.c";
void leak(int32** out) {
    consumes out[0..1];
    produces out[0..1];
    ensures *out[0] == 3;
} by { execute(); simp(); }
```

```expect
fail: checked outcome `simp` search did not retain a complete proof
```
