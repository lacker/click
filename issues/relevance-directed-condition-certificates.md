# Make condition-certificate search relevance-directed

## Problem

While restoring the general `vector_push` call in the owned-vector pipeline,
`execute_until(statement(4))` crosses the two-second smart-tactic budget. The
slow path is not C execution. Certificate planning asks whether a theorem
premise can be reconstructed from the ambient condition facts, and one
non-derivable equality over a wide memory snapshot consumes essentially the
whole budget in `bounded_condition_derivation`.

The old implementation hid a related problem behind two arbitrary choices: it
looked at only the first 48 condition facts and then tried every singleton and
pair. Removing that prefix and quadratic pair search is necessary, but running
the full condition theory for every unrelated candidate is still too
expensive. Raising the depth threshold, adding another fact-count cutoff, or
accepting the slow success would merely move the failure.

## Violated invariant

A smart tactic must either produce a replayable certificate within its local
budget or fail promptly with an actionable reason. Certificate reconstruction
must depend on facts relevant to the requested proposition, not on the total
width of an accumulated symbolic memory state.

## Intended regression

Keep the source-faithful owned-vector pipeline shape in which:

1. `vector_init` establishes caller-supplied storage;
2. the unchanged general `vector_push` is called modularly; and
3. a later modular call requires facts carried across those snapshots.

The focused command is:

```text
click verify examples/owned-vector/vector.click:806:5
```

At the current reduction, the active `execute_until` spends about two seconds
trying and failing to derive an equality between a fresh symbolic value and a
load from a wide prior snapshot. A smaller unit regression should retain that
shape: many irrelevant condition facts, a wide snapshot term, and a requested
fact that is not derivable. It must also cover a genuinely derivable
three-premise condition so relevance filtering does not become incompleteness.

## Design direction

Build a dependency slice for the requested condition before invoking general
reasoning. Equality and order facts can contribute only when their operands or
symbolic dependencies connect to the goal; extend that slice transitively and
ask the kernel for one proof-producing derivation over the slice. Preserve the
derivation's exact context premises for replay.

If snapshot equality needs special handling, traverse the memory-derivation
DAG by the loaded address instead of structurally cloning and comparing every
cell in each snapshot. Do not use a wall-clock check, term-count cap, or a new
magic prefix as the semantic filter.

## Acceptance criteria

- The focused owned-vector proof unit stays below the two-second smart-tactic
  budget without changing its C or adding irrelevant Click bookkeeping.
- A non-derivable condition over a wide snapshot fails promptly.
- Derivations needing three or more relevant facts still produce replayable
  certificates, regardless of where those facts occur in the ambient context.
- Search and replay agree on the exact premises used.
- Normal diagnostics summarize the failed condition without dumping the full
  embedded memory state.
- Profile, expansion, audit, and the default test suite pass before resuming
  the vector feature.
