# A missing theorem premise inside a model match is reported locally

The written `apply` needs `x == 0`, but the contract supplies `x == 1`.
A model-match arm must retain the theorem selector's refusal, as a linear
proof does, rather than reporting an unsupported proof shape.

```c filename=probe.c
void put(int32 *p, int32 x) { *p = x; }
```

```click
verifying "probe.c";
spec enum Model { One, Two }
resource box(p: int32*) { field model: Model; owns *p; }
theorem zero(x: int32) { requires x == 0; ensures x == 0 by { close(); } }
void put(int32* p, int32 x) {
    consumes b: box(p);
    requires x == 1;
    produces *p;
    ensures 1 == 1;
} by {
    match b.model {
        Model::One => { apply(zero(x)); unfold(b); },
        Model::Two => { unfold(b); },
    }
}
```

```expect
fail: theorem `zero` has an unproved obligation: `x == 0`
```
