# Contract refinement has no execution frontier

A contract-refinement theorem that executes no C is a pure proof, so
`step_until(function.exit)` has no frontier to step from and is refused.

```click
contract int32 Source(int32 x) { ensures result == x; }
contract int32 Target(int32 x) { ensures result == x; }

theorem lift(callback: int32 (*)(int32)) {
    requires Source(callback);
    ensures Target(callback) by {
        unfold(Source(callback));
        unfold(Target(callback));
        step_until(function.exit);
        close();
    }
}
```

```expect
fail: tactic `step_until` is not available in the pure proof for theorem `lift`
```
