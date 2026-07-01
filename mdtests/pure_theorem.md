# pure theorem declarations

This checks that a `.click` file can declare and verify a pure theorem without
attaching the proof to a C function.

```click
theorem preserves_assumption(x: int32) {
    requires x >= 0;

    ensures x >= 0 by auto;
}
```

```expect
pass
```
