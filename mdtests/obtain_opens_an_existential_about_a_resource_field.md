# Obtain opens an existential about a resource field

```c filename=check.c
void check(int p) {}
```

```click
verifying "check.c";

spec enum Model { A, B }
resource ghost(id: int32) { field model: Model; }

void check(int32 p) {
    owns state: ghost(0);
    requires state.model == Model::A;
    ensures true;
} by {
    have exists (w: int32) { w == p and state.model == Model::A } by {
        witness(p);
        solve();
    }
    let k = obtain(exists (w: int32) { w == p and state.model == Model::A });
    have k == p by known();
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
