# generic theorem declarations require checked monomorphization

Generic pure functions and predicates are instantiated when lowered. A
generic theorem cannot be admitted as an unchecked axiom schema: Click must
first verify the same concrete instance that a proof later applies.

```click
theorem reflexive<T>(value: T) {
    ensures value == value;
}
```

```expect
fail: generic theorem `reflexive` requires use-site monomorphization, which is not supported yet
```
