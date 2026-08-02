# Unify the execution tactics

## Problem

Click currently exposes `step`, `execute_step`, branch-specific step tactics,
`execute_rest`, `execute_until`, `bounded_execute`, loop-summary application,
and `advance`. Their names mix execution extent, automation strength,
implementation strategy, and historical accidents. A user cannot predict from
the vocabulary which operation to choose or which spelling expansion will
produce.

This issue establishes one small execution vocabulary and one consistent rule
for the smart and simple forms. It follows
[tactic-vocabulary-cleanup.md](tactic-vocabulary-cleanup.md), which performs the
mechanical renames to `execute`, `summarize`, and `reach`.

## Target vocabulary

| Tactic | Meaning |
| --- | --- |
| `step()` | Smartly advance one small C transition, proving contextual prerequisites and transporting supported facts. |
| `step using { fact P; ... }` | Perform the same transition as one simple certificate step using exactly the listed premises. |
| `execute()` | Smartly execute from the current frontier to function exit. |
| `execute_until(point)` | Smartly execute from the current frontier to the selected forward point. |
| `summarize(loop(N))` | Smartly pass an already verified loop using its summary. |
| `summarize(loop(N)) using { fact P; ... }` | Apply that loop summary as one simple step using exactly the listed premises. |
| `reach(point) ensuring { ... } by { ... }` | Prove a scoped execution region and replace its frontier with the declared interface. |

For operations with both forms, the convention is:

- A bare operation may select facts or otherwise reason from ambient context,
  so it is smart.
- A `using` operation names the complete premise set and performs one bounded,
  deterministic rule, so it is simple.

Allow an empty `using {}` block when a context-free simple execution or loop
summary step needs a spelling distinct from the smart bare form. Expansion
must always emit the `using` form, including the empty form when there are no
premises.

## Retire redundant tactics

### `execute_step()`

Replace it with smart `step()`. The existing simple `step()` meaning moves to
the explicit `step using { ... }` form. This makes `step` the operation and
`using` the automation boundary, matching `apply` and `transport`.

### `execute_then_step()` and `execute_else_step()`

Remove both. Smart `step()` can infer the uniquely provable branch. An author
who wants an explicit proof split can use proof-level `if`; an expanded
certificate can select the branch with an exact condition fact in `step using
{ ... }`. Separate names for the two arms are redundant.

### `bounded_execute()`

Remove it from the surface language. A fixed search budget is an automation
policy, not a distinct proof intent. Branch exploration belongs in `auto` or
`execute()`, while time and step limits belong in tool options and diagnostics.
Successful automation must still expand to ordinary simple tactics.

### `execute_rest()` and `symbolic_execute()`

The vocabulary issue renames the canonical operation to `execute()` and
removes both historical spellings.

## Boundaries between the remaining operations

- `step` performs exactly one source transition.
- `execute_until` repeats contextual steps to a caller-selected point without
  introducing a new proof interface.
- `execute` repeats contextual steps to function exit.
- `summarize` crosses one verified loop as an opaque transition.
- `reach` creates a nested proof scope and exposes only its declared facts and
  resources afterward. It is control flow, not repeated execution shorthand.

Diagnostics should explain these boundaries in user terms. They should not ask
the user to choose between “straight-line replay,” “certificate alternatives,”
or a “bounded executor.”

## Expansion, profiling, and audit

- Every successful `step`, `execute`, `execute_until`, and `summarize` must
  retain a checked expansion made only from simple tactics and control-flow
  nodes with simple descendants.
- Expanded source must use `step using { ... }` and `summarize(...) using {
  ... }`; it must not contain smart execution tactics.
- `click profile` should attribute the outer smart call to its canonical name
  and its simple leaves to `step`, `summarize`, `transport`, and other surface
  concepts.
- `click audit` should discover and expand slow smart calls under their
  canonical names. Removing `bounded_execute` must not create an un-audited
  execution path.

## Acceptance criteria

- The surface execution inventory is exactly `step`, `execute`,
  `execute_until`, `summarize`, and control-flow `reach`.
- Bare `step` and `summarize` are smart; their `using` forms are simple and
  accept an empty exact-premise block.
- The retired spellings are rejected with focused migration errors.
- Expansion of every successful smart execution tactic produces canonical
  source that reparses and replays.
- Branching, loop entry, straight-line execution, function exit, and scoped
  region tests cover both author-facing and expanded forms.
- Profiler and audit tests cover the canonical names and classifications.
- All proof workflow, loop, language, tactics, and tooling documentation is
  updated in the same change.
- The default test suite passes.
