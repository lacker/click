# Make simple tactics fast: exact requirements, expandable `auto` for the rest

Priority: P1.

Soundness: not soundness. This is tactic architecture and performance. Every
derivation a simple tactic performs today is already kernel-checked; the
change is where the search runs, what it costs, and whether expansion shows it.

## Why this is P1

The 2026-10-12 launch design review (critique W3, moved here) found that
`step()` is labelled simple yet runs "with every fact in the proof context
visible" (`docs/reference/tactics/index.md`), while the work to make it simple
was paused. A launch audience reading the tactic reference would take the
simple/smart split at its word. The review proposed finishing this issue or
reclassifying `step()` as smart; [design-review.md](design-review.md) depends on
this issue for that critique.

## Decision

Decided 2026-10-13 by the maintainer, ruling on that critique: fix, without
reclassifying `step()`. `step()` stays a simple tactic and
`execute()` stays a sequence of steps plus the proof structure a single step
cannot express (branches, path selectors, loop walks). What a simple tactic
must be is fast: its checking is bounded by the selected operation, its
explicit inputs, indexed context lookups, and the proof-state delta. It never
searches the whole proof context.

The general rule, for every simple tactic and not only `step()`:

1. A simple tactic has a set of *requirements*: every check that can fail for
   it, including call preconditions, the condition fact that selects an `if`
   arm or loop exit, memory safety of each access, and arithmetic that would
   otherwise be undefined.
2. Each requirement is first tried by the *fast path*: an exact or indexed
   lookup, or a bounded local kernel decision about the affected operation.
3. A requirement the fast path does not close is discharged by an implicit
   `auto` at the tactic's pre-state. That `auto` cannot advance C.
4. Expansion prints that proof attached to the tactic, so the expanded proof
   needs no search and verifies cold with implicit `auto` disabled.

Every requirement must have a faithful Surface spelling that re-lowers to its
exact kernel proposition. This is an invariant of the language, not a case a
tactic handles by refusing: a requirement Click cannot spell is a defect, filed
in `bugs/` and fixed by building the spelling where the requirement is created
or, with maintainer approval, by adding syntax that names the value.

### Syntax

A tactic whose requirements leave exactly one obligation after the fast path
takes a plain `by`, as `close_invariants by` does:

```click
step() by { arithmetic() using { ... }; }
```

When several remain, the tactic takes a block with one `requires` entry per
obligation, the way `loop { ... }` takes `initialize by` and `preserve by`:

```click
step() {
    requires p != null by auto;
    requires i < len by arithmetic() using { ... };
}
```

- Each `requires P by ...` must match exactly one remaining obligation; a
  proposition that matches none or more than one fails where it is written.
- An obligation not written is closed by the fast path, then implicit `auto`.
- A plain `by` when more than one obligation remains fails and lists each
  remaining obligation in Surface syntax, ready to copy into `requires` lines.
  A plain `by` or `requires` entry when the fast path already closes every
  obligation fails as superfluous, as an unneeded `close_invariants by` does.
- `requires name: P by ...` is accepted where a label helps; no obligation
  needs one.
- Expansion prints plain `by` when exactly one obligation needed `auto`, and
  `requires` entries when several did.

Which obligations remain depends on the context, so a context change can turn
a plain `by` into a refusal. That failure is prompt and names the new
obligation; the meaning of a proof never changes silently. This fragility is
accepted.

## Current state

Measured on `aa30a5f`.

A bare `step()` is checked under `StatementPrerequisitePolicy::Retained` with
the whole proof context (`src/surface/proof/proof_object/execution_statements.rs`).
Three routes derive prerequisites without retaining them:

- **Call and access obligations.** A non-exact obligation falls back to
  `derive_proposition`
  (`src/surface/proof/execution_planning/transition_certification.rs`), the
  general search in `src/surface/planning/proposition_search.rs`: conjunction
  and disjunction projection, implication, `forall` instantiation, and
  bounded case splits. The checked derivation is stored in
  `prerequisite_derivations`, which nothing reads.
- **Condition prerequisites.** A boolean `proves()` over the same context,
  with no derivation recorded.
- **In-step re-run.** A refusal whose antecedent is a retained `have` is
  re-checked as `Contextual` (`src/surface/proof/checked_drivers/statement_step.rs`).

Smart execution retries a refused step after constructing a `have`
(`retry_statement_after_refusal` in `src/surface/proof/smart_closures.rs`),
but `requirement_uses_planning_compatibility` sends every unsupported shape
back through the hidden search.

Earlier work toward the previous design is landed and reusable:

- Caller-requirement identity (`src/surface/source_registry.rs`):
  `RequirementSourceId`, `EntryFactOrigin`, and
  `lookup_unique_caller_requirement`, with `Choose` revalidating the
  selection. This spells the caller-requirement shape of obligation.
- Generated-load source events (`src/kernel/primitives.rs`): `LoadSourceId`,
  `GeneratedLoadSourceEvent`, and per-transition `Unique`/`Ambiguous`
  resolution. No consumer reads them yet, and `LoadSourceId` has no region or
  spelling. It is the starting point for spelling load equations, if the
  census shows they need it.

## Plan

Each step is its own pull request.

### 1. Census (landed)

`instrumentation::HiddenPrerequisiteRoute` counts each hidden derivation by
route and top derivation rule, and both fixture harnesses ratchet it
(`docs/internals/testing.md`). Library tests read the same events per step
through `collect_planning_statement_transitions`, which had recorded nothing
since the old `Planning` policy was removed.

Baseline on the unfiltered corpus, all under `StepObligation`:

| Rule | mdtests | examples |
| --- | --- | --- |
| `And` | 22 | 4 |
| `Implies` | 12 | 0 |
| `ContextualAtomic` | 12 | 0 |
| `FiniteForAll` | 1 | 0 |

The 47 mdtest derivations come from 24 files, nearly all
`authority_*`/`population_*` counting and `shared_heap_*` lifecycle tests, plus
`strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts`. Condition
prerequisites, loop-phase `Contextual` checking, and the retained-`have`
re-run record none. Still uncounted: the kernel's own condition evaluation
under `Retained`, which does not defer non-exact condition reasoning
(`certified_condition_transitions`), and the spellability and work of each
derivation. Add those before cutting over the routes they affect.

### 2. Requirement driver and syntax

One shared driver per simple tactic: build each obligation with its Surface
spelling where the obligation is created (a callee clause with the call's
argument expressions substituted, an access expression at its program point),
try the fast path, then implicit `auto`, and record the expandable proof.
Implement `Tactic() by { ... }` and `Tactic() { requires P by ...; }` for
`step()` and the call forms first. Smart execution's retry and the in-step
`Contextual` re-run move onto this driver. A debug assertion checks that each
spelling re-lowers exactly.

### 3. Cut over by shape

Most frequent census shapes first. Each shape that moves to the driver
lowers the census baseline. A shape without a spelling is a bug fixed as
described above. Extend the driver to the other simple tactics with
prerequisites.

### 4. Remove the hidden search

Delete the remaining hidden derivation from simple checking, the
compatibility escape hatch, and the in-step re-run. Add deterministic scaling
regressions showing simple-tactic cost does not grow with unrelated context
facts. Cold-check the expanded corpus with implicit `auto` disabled, and run
`scripts/check.sh` unfiltered.

Implicit `auto` has its own budget, and profiling attributes its work to
`auto`, not to the simple tactic, so a slow `auto` is not reported as a slow
step.

## Acceptance criteria

- No simple tactic performs a search over the proof context; its cost is
  bounded by its operation, explicit inputs, indexed lookups, and delta.
- Every requirement has a Surface spelling that re-lowers exactly; the census
  of unspellable requirements is zero.
- A requirement the fast path does not close is proved by implicit `auto`, and
  expansion prints it as `by` or `requires P by` on the tactic.
- The expanded corpus verifies with implicit `auto` disabled.
- Removing a required `by` body or `requires` entry from an expanded proof
  fails at that obligation in a minimal regression.
- `docs/reference/tactics/index.md` documents the requirement rule, the fast
  path, and both syntax forms, each backed by an mdtest.
- Production C is unchanged. `scripts/check.sh` passes, and both fixture
  harnesses report a zero hidden-derivation census.

## Not in scope

- Recursive-call `decreases` obligations.
- Completeness of `auto`.
- Changes to verified C made only to simplify a proof.
