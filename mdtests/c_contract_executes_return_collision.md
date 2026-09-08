# The result binder cannot replace the executed callback parameter

```click
contract int32 Raw(int32 x) { ensures result == x; }
theorem lift(result: int32 (*)(int32)) executes result(int32 value) {
    requires Raw(result);
    ensures Raw(result) by { step(Raw); simp(); }
}
```

```expect
fail: callback parameter must not be named result
```
