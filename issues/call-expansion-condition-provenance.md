# Record condition provenance across opaque calls

Smart call planning can discharge a callee precondition, a contract-expression
load, or a path choice directly from the ambient condition context. The
resulting transition records the successful outcome but not which conditions
made it possible. `click expand` therefore has only two bad choices: copy the
entire proof history into `step() using`, or omit a condition that replay needs.

This is distinct from stale ambient loadability permissions, which can be
filtered by snapshot unless an explicit prerequisite selects them. Conditions
can remain relevant across unrelated memory changes, so snapshot age is not a
sound relevance test.

An attempted fix that retained every satisfied call requirement as an ordinary
kernel obligation exposed a second constraint: the authoritative execution
path must not change. The `allocated-linked-list` example replayed different
opaque-call identities from final kernel certification, and `input-cursor`
lost a transport premise. A separate cloned-budget lowering pass avoided
counter mutation but did not by itself make multi-path provenance complete.

## Regressions

- A caller establishes several historical inequalities, then makes a final
  opaque call whose contract needs none of them. Expansion of the final call
  must omit those old conditions.
- A call precondition that reads memory must expand with both the precise
  condition and the loadability needed to evaluate it.
- `allocated-linked-list` must retain identical replay and certification paths.
- `input-cursor` must retain the exact source facts required by its
  post-execution transports.

## Acceptance criteria

- Planning records every ambient condition actually used by call-contract
  lowering, path selection, mutable-footprint evaluation, and fact transport.
- It does not record unrelated ambient conditions.
- Provenance collection does not consume or renumber opaque-call or
  verification-variable identities.
- The expanded certificate replays using only those recorded premises.
- The focused regressions, library suite, and all non-quarantined examples are
  green without changing example C or proof structure.
