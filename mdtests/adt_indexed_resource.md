# ADT-indexed resource

A resource index is an ordinary symbolic Click value, not a C parameter or a
value stored in the owned cell. Here `mark` is arbitrary: declaring the
resource must not require choosing `Mark::Clear` or `Mark::Set`, executing a
match, or expanding the index into constructor cases.

```click
spec enum Mark {
    Clear,
    Set,
}

resource marked_cell(p: int32*, mark: Mark) {
    owns p[0..1];
}
```

This is the current declaration-level blocker for
[ADT-indexed resources](../issues/algebraic-data-types.md), not a passing
ownership proof. The exact rejection is intentional for now: change this
expectation to `pass` when symbolic resource arguments are implemented.

```expect
fail: resource `marked_cell` parameter `mark` uses an algebraic type; algebraic resource arguments are not supported yet
```

The next end-to-end regression should read the cell while preserving
`marked_cell(p, m)` for an arbitrary symbolic `m: Mark`, exercising explicit
fold/unfold and function-contract transfer. It needs the contract model-binding
support tracked in the same issue; this fixture does not invent syntax for
that unfinished path.

Separate negative fixtures should then reject an unjustified change of index
and duplicated ownership, while a proved index equality should permit
substitution. They must reach those checks rather than merely pass because
the declaration is currently unsupported.

The index here is only a label. Relating `Mark::Clear` and `Mark::Set` to cell
contents through resource `match` is a subsequent slice.
