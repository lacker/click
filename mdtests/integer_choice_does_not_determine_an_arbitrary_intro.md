# Logical choices remain independent of universal witnesses

```click
theorem choice_is_not_universal() {
    requires exists (x: Integer) { x == 0 };
    ensures forall (arbitrary: Integer) { arbitrary == 0 } by {
        intro();
        obtain (chosen: Integer) { chosen == 0 }
        assumption();
    }
}
```

```expect
fail: requires the current goal as an available semantic fact
```
