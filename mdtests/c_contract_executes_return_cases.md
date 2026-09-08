# One return-valued call per proof case

```click
contract int32 Raw(int32 x) { ensures result == x; }
contract int32 Target(int32 x) { ensures result == x; }
theorem lift(callback: int32 (*)(int32)) executes callback(int32 value) {
    requires Raw(callback);
    ensures Target(callback) by {
        if value == 0 {
            step(Raw);
            have result == 0 by { simp(); }
            simp();
        } else {
            step(Raw);
            have result == value by { assumption(); }
            simp();
        }
    }
}
```

```expect
pass
```
