# `simp() using` expands to explicit simple certificates

Click currently treats `derive using { ... }` as a simple tactic because its
premises are explicit. That classification is wrong. The tactic still chooses
how those premises prove the current goal: it tries atomic normalization,
equality chains, arithmetic, pointer reasoning, memory-DAG transport, framing,
effect reconstruction, and increasingly broad ambient fallbacks. Explicit
hints constrain a search; they do not name a proof rule.

This ambiguity has made `derive` both a smart prover and its own purported
simple certificate. As new goals have needed to replay, the checker has grown
more fallback paths instead of expansion gaining the explicit proof rules it
needs. A small generated certificate can consequently perform seconds of
ambient proof-history search during deterministic replay.

Replace this design with two smart proposition tactics:

```click
simp();

simp() using {
    x < y;
    y < z;
}
```

`simp()` reasons from the applicable ambient proposition context.
`simp() using { ... }` reasons from exactly the listed facts plus
context-free kernel computation. Neither form executes C or silently consumes
ambient execution-effect facts. Cross-execution reasoning must be selected by
smart search and expanded into explicit transport/frame evidence.

The parentheses are intentional and match `step() using`, `frame() using`,
`transport(...) using`, and `apply(...) using`. `by simp;` remains the
standalone shorthand for ambient simplification; no additional shorthand is
required for the explicit-fact form.

`derive` should be removed completely rather than retained as an alias or
migration diagnostic. Click is unreleased and supports this codebase, so every
source, test, diagnostic, printer, and document can migrate together.

## Current implementation boundary

The `simp() using` foundation is now separate from legacy `derive`:

- it has its own AST payload and is classified as smart;
- planning checks availability but reasons from exactly the listed facts;
- certificate lowering consumes the selected restricted plan rather than
  checking the goal with `derive`;
- supported equality and pointer-alias derivations expand to `rewrite`,
  `assumption`, and `normalize`; and
- an unsupported derivation fails locally with a bounded missing-simple-rule
  diagnostic. It never falls back to `derive`, including after a generated
  certificate fails replay.

Legacy `derive` is intentionally still accepted so migrations can land one
green proof or project at a time. Its removal is the final phase, not part of
the foundation change.

## `auto`, `simp`, and simple replay

The intended boundary is:

- `auto` orchestrates a whole claim and may choose C execution, checked loop
  handling, effect framing, and proposition reasoning;
- `simp` proves the current pure proposition without moving the execution
  frontier, with `using` restricting its fact context; and
- a simple tactic checks one named rule from explicit evidence with work
  proportional to that certificate.

Smartness is about choosing the proof rule, not merely choosing premises.
Both `simp` forms must be profiled, expandable, and auditable as smart tactics.
Neither may appear in a completed expansion.

Expansion may use existing simple rules such as `assumption`, `normalize`,
`rewrite`, `transport(...) using`, `frame() using`, `apply(...) using`, and the
structural proposition rules. If an atomic derivation selected by `simp`
cannot be expressed through those operations, add the smallest explicit
surface proof rule needed to replay that derivation. Do not solve the gap by
moving the search back into a generically named “simple” checker.

## Owned-string regression

`examples/owned-string` exposes the current failure. Several nested
`have { derive using { ... } }` blocks take about 2.6s to 4.9s each. Two prove
that `owner->cap` or `owner->data` is unchanged while listing an unrelated
`owner->len` store equation. Their actual justification is hidden ambient
execution history.

During replay the reconstructed `old(...)` and current memory spellings do not
retain a usable execution-DAG connection. The checker then scans ambient
equalities, separation facts, and effect facts to rediscover a proof. Attempts
to reorder alias checks, cache the ambient assumptions, or run effect-chain
checks earlier do not repair the missing certificate and must not be used as
the fix.

The migrated proof should contain the explicit simple transport/frame
certificate chosen by `simp() using`, while preserving the existing C source
and the strength of every claim. Verification work should depend on that
certificate, not on the amount of irrelevant earlier snapshot history.

## Remaining migration blockers

The first completed source migration is `examples/binary-tree`: its int32,
pointer, and pointer-offset equality chains now expand to explicit `rewrite`
and `assumption` steps. Two other source shapes still need principled surface
certificates before their old `derive using` blocks can be removed:

- `examples/vector-push` proves `1 <= owner->len` after incrementing a
  nonnegative old length, and `examples/input-cursor` has the analogous
  `0 <= owner->pos` successor proof. Smart simplification verifies these
  arithmetic consequences, but equality rewrites alone cannot express the
  selected order rule. Add the smallest named simple arithmetic rule (or an
  equally explicit theorem application), not a generic arithmetic solver
  relabeled as simple.
- The owned-string replay/certification instability has been fixed and the
  project now passes repeated ordinary verification under its normal limit.
  Its remaining `derive using` sites can therefore be migrated as focused
  certificate-vocabulary work rather than treated as a baseline blocker.
- A listed fact exposed as one conjunct of an unfolded predicate has no simple
  conjunction-elimination rule yet. Restricted simplification now reports
  that missing vocabulary directly instead of hiding the extraction inside a
  generated `derive`.

The input-cursor attempt also exposed and fixed a separate lowering bug:
declaration expansion populated resource argument type metadata in `derive`
premises but omitted `simp() using` premises. A focused syntax regression now
keeps that metadata; the example reaches the arithmetic-certificate gap above
instead of failing resource lowering.

Keep affected proof sites unchanged until their focused regressions expand and
replay. Do not count retaining `derive using` as a workaround for either
replay or performance failures.

## Implementation order

1. Keep the strict `simp() using` foundation green. Its search uses exactly
   the listed facts, and every success must lower to a replayable `SimpleProof`
   without `derive`.
2. Migrate one independently comprehensible `derive using` proof or small
   project at a time. When a migration exposes missing certificate vocabulary,
   add the smallest named simple rule and its focused regression before
   continuing.
3. Re-expand or directly migrate owned-string only after its unchanged-field
   proofs select explicit transport/frame certificates rather than ambient
   reconstruction.
4. When no source or generated certificate depends on `derive`, delete its
   syntax, AST variant, printer, checker, diagnostics, tests, and
   documentation.

Each step must leave the repository green. Temporary coexistence during the
implementation is acceptable inside an uncommitted or intermediate green
chunk, but the completed issue has no compatibility alias or legacy syntax.

## Acceptance criteria

- `simp() using { ... }` uses exactly its listed proposition facts and is
  consistently classified as smart.
- `click profile`, `click expand`, and `click audit` agree about both `simp`
  forms.
- Expansion of either form contains only genuinely simple named proof rules
  and verifies as a complete proof unit.
- Simple replay never searches ambient equality classes, effect histories, or
  alternate proof strategies as a fallback.
- `derive` no longer exists in accepted syntax, internal tactic variants,
  diagnostics, tests, examples, or documentation.
- Focused tests distinguish `auto` orchestration, ambient `simp()`, restricted
  `simp() using`, and their expansions.
- A restricted simplification fails clearly when an omitted fact is required;
  it never succeeds by consuming that ambient fact implicitly.
- The existing owned-string C and claims verify under the normal 30s project
  limit, with no multi-second work attributed to simple or control replay.
