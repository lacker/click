# Retained parameter values do not grant a view of their expired storage

```c filename=aggregate_parameter_cannot_return_a_view.c
struct packet { int32 value; };
void leak(struct packet input, int32** out) { out[0] = &input.value; }
```

```click
verifying "aggregate_parameter_cannot_return_a_view.c";
void leak(struct packet input, int32** out) {
    consumes out[0..1];
    produces out[0..1];
    ensures viewable(out[0][0..1]);
} by { execute(); simp(); }
```

```expect
fail: kernel goal: viewable(
```
