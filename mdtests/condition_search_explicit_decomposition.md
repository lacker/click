# Explicit premises remain the condition-search escape path

Smart condition search is deliberately heuristic. This fixture checks that a
user can bypass it with the simple `derive using` tactic and exact relevant
premises.

```click
theorem equality_transitive_with_exact_premises(x: int32, y: int32, z: int32) {
    requires x == y;
    requires y == z;
    ensures x == z by {
        derive using {
            x == y;
            y == z;
        }
    }
}
```

```expect
pass
```
