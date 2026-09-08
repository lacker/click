# Non-void execution theorems expose the callback result

```click
contract int32 Raw(int32 x) { ensures result == x; }
contract int32 Target(int32 x) { ensures result == x; }
theorem lift(callback: int32 (*)(int32)) executes callback(int32 x) {
    requires Raw(callback);
    ensures Target(callback) by { step(Raw); simp(); }
}
```

```expect
pass
```
