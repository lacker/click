# Synthesized model equalities preserve address-only pointer casts

The pure theorem controls constructor exclusion. The C caller needs the same
exclusion from an opaque call's produced resource. Synthesis must retain the
`void*` cast when reconstructing the checked equality, so its rewrite has the
same typed constructor as the original postcondition.

```c filename=case.c
struct child { int value; };
void attach(struct child* kid) {}
void caller(struct child* kid) { attach(kid); }
```

```click
verifying "case.c";
spec enum Model { Empty, At(void*), }
resource box() { field model: Model; }
void attach(struct child* kid) {
    produces held: box();
    ensures held.model == Model::At(kid as (void *));
} by { step_until(function.exit); let held = fold(box(), {model: Model::At(kid as (void *))}); close(); }
void caller(struct child* kid) { ensures true; } by {
    let {held: held} = step(attach);
    have held.model != Model::Empty by close();
    step(); close();
}

theorem excludes(p: void*, m: Model) {
    requires m == Model::At(p);
    ensures m != Model::Empty by close();
}
```

```expect
pass
```
