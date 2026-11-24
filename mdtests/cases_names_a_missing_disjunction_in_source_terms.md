# `cases` names a missing disjunction in source terms

`cases { A => { ... } B => { ... } }` splits on the disjunction of its arms,
which must follow from the available facts. When it does not, the refusal spells
the disjunction in source terms, not as a dump of the kernel's internal
proposition.

```click
theorem reflexive(x: int32) {
    ensures x == x by {
        cases { x > 0 => { close(); } x < 0 => { close(); } }
    }
}
```

```expect
fail: `cases` could not prove that its alternatives are exhaustive: `x > 0 or x < 0`
```
