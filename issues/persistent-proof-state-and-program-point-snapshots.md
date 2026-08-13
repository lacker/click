# Statement replay clones accumulated proof history and full symbolic states

Program points are stored as `BTreeMap<ProgramPointRef, CState>`. During
surface construction of each statement step, Click clones the complete map,
records more full `CState` values, diffs the maps, and clones successor states
again. `CState` owns local bindings, `CMemory` maps, a resource vector, and
counted populations.

A straight-line function can therefore take quadratic time and space even
when its proof is only a sequence of explicit `step()` tactics. Snapshot
history also retains far more state than most later `at(...)` expressions
reference.

## Required design

Represent symbolic state and program-point history with immutable structural
sharing. A statement transition should create a state delta and one snapshot
handle; recording or temporarily viewing a program point must not copy prior
history. Preserve stable snapshot identity for lowering, diagnostics, and
memory-derivation reasoning.

Consider separating locals, memory, resources, and population stores so a
scalar assignment does not copy unrelated heap or resource structures. The
surface-construction override mechanism should use a scoped overlay rather
than clone-and-diff.

## Regression design

Generate one function with increasing numbers of straight-line scalar
assignments and explicit simple steps. Add a second variant with sparse
`at(statement(...), ...)` references to prove that retained history stays
available without changing the growth curve. Measure work and retained state
or allocation counts where practical.

## Acceptance criteria

- Recording one new program point is logarithmic or better in prior points.
- A local scalar transition does not deep-clone memory or resources.
- Straight-line simple replay passes the statement-count scaling gate.
- Snapshot lowering and the memory DAG retain exact replay semantics.
- Existing expansion and program-point tests remain green without source
  changes.
