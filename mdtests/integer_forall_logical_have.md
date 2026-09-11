# Integer logical nested have retains the promoted binder

```click
theorem integer_forall_logical_have() {
    ensures forall (z: Integer) { z == z and z == z } by {
        intro();
        have z == z and z == z by { simp(); }
        assumption();
    }
}
```

```expect
pass
```
