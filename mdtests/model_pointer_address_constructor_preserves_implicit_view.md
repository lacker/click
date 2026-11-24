# Synthesized model equalities preserve implicit pointer views

The opaque call retains the struct pointer's full saved view in a `void*`
model field. Synthesizing its constructor equality must use implicit coercion
rather than introducing an explicit cast that would widen that view.

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
    ensures held.model == Model::At(kid);
} by { step_until(function.exit); let held = fold(box(), {model: Model::At(kid)}); close(); }
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
