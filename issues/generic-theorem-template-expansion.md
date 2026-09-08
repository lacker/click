# Expand generic theorem templates

## Violated invariant

A source-level proof should have an actionable expansion path. Generic theorem
templates are checked at concrete applications, not returned as universally
checked certificates by the theorem verifier. Expanding a tactic inside a
template therefore has no concrete certificate to render.

Source-location lookup now accepts generic parameter lists, and expansion
reports that a concrete type instance is required rather than claiming that
the theorem or ensure is missing. Expansion of concrete clients works.

## Intended regression

Retained in `generic_template_expansion_reports_missing_instantiation` in
`src/surface/expansion/tests.rs`:

```click
theorem client<T>(xs: List<T>, ys: List<T>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 0 by {
        normalize() using { not(xs == ys); }
    }
}
```

## Acceptance criteria

- Decide whether template expansion checks a genuinely parametric certificate
  or requires an explicitly selected concrete instance. Do not choose an
  arbitrary concrete type silently.
- Verify before expanding, render a source-correct proof, and recheck it.
- Cover simple and smart tactics, multiple type parameters, invalid template
  bodies, and concrete clients.
- Preserve the actionable diagnostic until template expansion is supported;
  then replace the retained refusal regression with successful rechecking.
