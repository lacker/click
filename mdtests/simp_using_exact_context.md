# `simp() using` restricts smart reasoning to named facts

The explicit-premise form remains smart because it chooses the reasoning
steps, but it considers only the named propositions.

```click
theorem equality_transitive_from_exact_context(x: int32, y: int32, z: int32) {
    requires x == y;
    requires y == z;

    ensures x == z by {
        simp() using {
            x == y;
            y == z;
        }
    }
}
```

```expect
pass
```
