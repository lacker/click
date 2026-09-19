# pure theorem rejects resource conclusions

This checks that theorem declarations stay pure: a theorem cannot return a
resource to the caller's resource context. Applying a theorem creates nothing
and returns nothing, so a `produces` clause has nothing to hand back.

A theorem can still say that a range is readable, as a hypothesis rather than a
conclusion: `views v[lo..hi];` among its requirements. A theorem's `ensures`
clauses are propositions, and `ensures viewable(...)` remains one of them.

```click
theorem resource_conclusion_is_not_pure(p: int32*) {
    produces p[0..1] by auto;
}
```

```expect
fail: pure theorem `resource_conclusion_is_not_pure` cannot conclude a resource: applying a theorem creates and returns nothing. A theorem states that a range is readable with `views v[lo..hi];` among its requirements, and concludes propositions only
```
