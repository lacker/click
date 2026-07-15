# pure theorem rejects resource conclusions

This checks that theorem declarations stay pure: a theorem cannot return a
resource to the caller's resource context.

```click
theorem resource_conclusion_is_not_pure(p: int32*) {
    ensures write(p[0..1]) by auto;
}
```

```expect
fail: `ensures` accepts pure propositions only; use `owns` or `produces` for owned output
```
