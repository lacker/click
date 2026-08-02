# Canonicalize the tactic vocabulary

## Problem

Click's core proof vocabulary is mostly conventional, but several surface
names describe implementation machinery rather than proof intent. There is
also one legacy alias, and internal certificate names leak into timing output.
This makes the language look larger and less regular than it is.

This issue is the mechanical first step. It deliberately does not change which
proofs tactics can establish. The related execution and semantic changes are
tracked separately in
[tactic-execution-unification.md](tactic-execution-unification.md) and
[tactic-semantic-consistency.md](tactic-semantic-consistency.md).

## Naming policy

- Keep established proof-language vocabulary when Click implements the usual
  concept: `auto`, `simp`, `apply`, `assumption`, `normalize`, `intro`, `left`,
  `right`, `contradiction`, `rewrite`, `have`, `unfold`, and `fold`.
- Keep a Click-specific name when the operation is genuinely specific to
  symbolic C execution, memory snapshots, or resources.
- Name tactics after the user's proof intent, not the certificate object,
  replay algorithm, search budget, or kernel backend.
- Give one operation one canonical spelling. Do not retain permanent aliases.
- Internal Rust variant names may remain descriptive, but user-facing source,
  diagnostics, expansion, profiling, and audit output should use the canonical
  surface vocabulary.

Parentheses and the general shape of tactic syntax are not part of this issue.

## Mechanical naming changes

| Current spelling | Canonical spelling | Reason |
| --- | --- | --- |
| `conjunction()` | `split()` | `split` is the familiar name for decomposing a conjunction goal and is an action rather than a connective name. Preserve the current exact-facts behavior in this issue. |
| `apply_loop_summary(loop(N))` | `summarize(loop(N))` | The user is passing a verified loop abstractly; `apply_loop_summary` exposes the implementation object and repeats information already present in `loop(N)`. |
| `execute_rest()` | `execute()` | Execution already begins at the current frontier, so `rest` adds no useful distinction. |
| `symbolic_execute()` | remove | It is a legacy alias for `execute_rest()` and should not survive the canonical rename. |
| `advance(point) ensuring { ... } by { ... }` | `reach(point) ensuring { ... } by { ... }` | Success means reaching the point and establishing its interface; `reach` states that postcondition directly. |

Update every repository-owned `.click` file, test fixture, diagnostic, help
string, example, and documentation reference atomically. Because Click is
still evolving, old spellings should produce a focused migration error rather
than remain accepted aliases. The error should name the replacement, except
for `symbolic_execute`, whose replacement is `execute()`.

## Names deliberately retained

- `derive`, pending its consolidation with `calculate` in the semantic issue.
- `transport`, because moving a fact between explicitly named execution
  snapshots is a real user-visible operation.
- `observe`, because it clearly describes projecting a non-consuming view of a
  held resource.
- `frame`, `choose`, `witness`, and proof-level `if`.
- `close_invariants()`. It is unusual, but accurately names the explicit
  certificate leaf that discharges the invariant bundle at a loop back edge.
  Keep it documented as advanced/certificate-facing rather than presenting it
  as an everyday tactic.
- `execute_until(...)`, until the execution vocabulary is handled by the next
  issue.

## Profiler and audit vocabulary

Users should not need to learn the internal certificate language in order to
read `click profile` or `click audit`. Keep internal names in detailed debug
output if useful, but group and label ordinary output by canonical concepts:

| Internal label | User-facing concept |
| --- | --- |
| `certified_statement_step` | `step` |
| `certified_loop_summary_step` | `summarize` |
| `certified_fact_transport`, `finish_certified_fact_transports` | `transport` |
| `certified_path_assumption` | `if` or the enclosing tactic that selected the path |
| `certified_frame` | `frame` |
| `exact_proposition_derivation` | `derive` |
| `certified_alternatives` | the enclosing smart tactic, not a new surface tactic |

The verifier remains the authority for simple/smart classification. Neither
the profiler nor audit should infer classification from these display names.

## Acceptance criteria

- The parser accepts the canonical spellings and rejects the old spellings
  with migration-oriented errors.
- Expansion emits only canonical, parseable source.
- Repository examples and tests contain no old spellings except negative
  parser tests and migration diagnostics.
- Normal profiler and audit reports use canonical surface concepts; internal
  labels are clearly secondary when shown.
- `docs/proof-tactics.md`, `docs/proof-landscape.md`, the language guide,
  intermediate guides, and examples agree on the new vocabulary.
- The default test suite passes.
