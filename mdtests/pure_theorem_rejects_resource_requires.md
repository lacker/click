# pure theorem rejects resource requirements

This checks that theorem declarations stay pure: a theorem cannot require a
resource from the caller's resource context.

```click
theorem resource_requirement_is_not_pure(p: int32*) {
    requires write(p[0..1]);

    ensures 0 == 0 by auto;
}
```

```expect
fail: pure theorem `resource_requirement_is_not_pure` currently supports proposition `requires` clauses only
```
