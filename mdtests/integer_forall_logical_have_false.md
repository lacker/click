# Integer logical nested have rejects a false conjunction

```click
theorem integer_forall_logical_have_false() {
    ensures forall (z: Integer) { z == z and z != z } by {
        intro();
        have z == z and z == 0 by { simp(); }
        assumption();
    }
}
```

```expect
fail: could not lower `have` proposition
```
