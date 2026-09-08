# A tautological result condition does not excuse skipping the call

```click
contract int32 Raw(int32 x) { ensures result == x; }
contract int32 Target(int32 x) { ensures 1 == 1; }
theorem lift(callback: int32 (*)(int32)) executes callback(int32 value) {
    requires Raw(callback);
    ensures Target(callback) by { simp(); }
}
```

```expect
fail: execution
```
