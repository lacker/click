# `simp() using` does not consume omitted ambient facts

The explicit-premise form is a restricted smart tactic. Facts in the ambient
theorem context are unavailable unless the `using` block names them.

```click
theorem omitted_fact_is_not_ambient(x: int32, y: int32, z: int32) {
    requires x == y;
    requires x == z;

    ensures x == z by {
        simp() using {
            x == y;
        }
    }
}
```

```expect
fail: `simp() using` could not prove the current goal from only its listed premises
```
