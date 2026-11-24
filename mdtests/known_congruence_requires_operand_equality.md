# Function application congruence needs equal arguments

```click
function opaque(x: int32) -> int32 { x }
theorem unrelated(x: int32, y: int32) {
    requires opaque(x) == 1;
    ensures opaque(y) == 1 by close();
}
```

```expect
fail: known
```
