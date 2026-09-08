# Contract refinement has no execution frontier

```click
contract int32 Source(int32 x) { ensures result == x; }
contract int32 Target(int32 x) { ensures result == x; }

theorem lift(callback: int32 (*)(int32)) {
    requires Source(callback);
    ensures Target(callback) by {
        unfold(Source);
        unfold(Target);
        execute();
        simp();
    }
}
```

```expect
fail: tactic `execute` is not available in the pure proof for theorem `lift`
```
