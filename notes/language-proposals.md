# Click Language Design Proposals

*Parked — these are deliberate language expansions, out of scope for the
short-term plan (`plan.md`). Revisit when the owner opens a language arc.*

Proposals for the three open language-design problems from the design review:
write-only proofs, verbosity without abstraction, and the three overlapping
memory-concept families. Each proposal is scoped to stay compatible with the
megakernel philosophy and the existing certificate architecture (smart tactics
plan, simple certificates replay).

---

## Problem A: Proofs are write-only

Exact-spelling fact matching, positional indices, and order-sensitive one-shot
closers couple every proof script to source coordinates and internal normal
forms. Evidence: `apply` refuses `x > 0` against premise `x >= 0`
(mdtests/theorem_apply_requires_exact_fact.md); `step()` fails even when the
contract literally contains the needed `requires`
(mdtests/simple_statement_step_requires_exact_prerequisite.md);
`statement(5).entry` and `choose(k from requirement 0)` break on any edit;
a `simp()` ordered before its enabling `have` fails permanently
(mdtests/grouped_post_tactics_respect_order.md).

### A1. A match-modulo-normalization tier for every exact matcher

Give `apply`, `step`, `fold`, and `frame` a three-stage matching ladder:

1. **Syntactic equality** (today's behavior, always tried first).
2. **Normalization equivalence**: alpha-equivalence plus the arithmetic
   normal form `simp`/`normalize` already compute (commutative-associative
   ordering, constant folding, canonical inequality direction). The kernel
   already owns this code; the change is calling it from the matchers.
3. **Bounded entailment** (opt-in, possibly per-tactic spelling like
   `apply!`): the existing `Assumptions::proves` with small fuel.

The certificate contract is preserved by making stages 2–3 *plan* extra
simple steps: a stage-2 match records the `normalize`/`rewrite` bridge, a
stage-3 match records the derivation as explicit `have` premises (the
machinery `TransportUsing`/`StepUsing` already does exactly this for smart
transport). Replay stays syntactic and cheap; user-facing scripts stop
breaking on `n + 1` vs `1 + n`.

Cost: medium (kernel matcher plumbing). Payoff: the single largest
brittleness reduction available; contracts and statements can be edited
without invalidating every dependent script spelling.

### A2. Names, not positions

- **Requirements**: `choose(k from requirement 0)` gains a labeled form
  `choose(k from bounds)` referring to `requires bounds: ...;`. Numeric
  indices keep working but produce a deprecation warning; a rewriter mode of
  `click-expand` auto-labels unlabeled requirements and upgrades call sites
  in one pass (the expansion infrastructure already does source-preserving
  rewrites, so this is a natural extension).
- **Statements**: `as label` statement naming already exists but even the
  in-repo examples use positional `statement(5).entry`. Make labels the
  documented primary spelling, add the same deprecation warning for bare
  positional references in committed files, and give the rewriter an
  auto-labeling mode (derive labels from the statement text, e.g.
  `after_init` / `store_len`).

Cost: small. Payoff: proof scripts survive edits to the C body and contract
ordering; positional forms remain for interactive exploration.

### A3. Two-phase grouped proofs (declarative closers)

The one-shot, order-sensitive closer model contradicts the declarative look
of the scripts. Split grouped post-execution blocks into the two phases they
already informally have:

- **Establishing steps** (`have`, `fold`, `unfold`, `apply`, execution
  tactics) run in source order, exactly as today.
- **Closing steps** (`frame()`, `simp()`) become *deferred*: they mark which
  claim families to close, and closure runs once at the end of the block
  against the final fact set.

Equivalently: after the last tactic, unclosed claims get one final closing
attempt with all established facts. Deterministic, certificate-friendly (the
certificate records the final closure), and it deletes the "simp before have
permanently fails" trap. Scripts that worked before still work — this only
adds successes, never removes them. If silent reordering is a concern, keep
strict mode behind a per-file or per-proof flag during migration.

### A4. Goal-state introspection (supporting tool)

Repairing a proof is write-only mostly because failure output speaks Kernel
Click. Add `click-verify --goals FILE:LINE:COL`: print the unclosed claims
and the available facts *in surface syntax* at the selected proof site,
using the existing surface printer. This is tooling, not language, but it
converts trial-and-error editing into targeted repair and pairs with A1–A3.

---

## Problem B: Verbosity with no abstraction mechanisms

~5:1 spec-to-code ratios (owned-string: 130 C lines → 691 Click lines);
an 18-fact `step using` block repeated four times in vector.click;
`int32_equality_transitive` copy-pasted into 5 of 6 example projects;
`empty_vector`/`nonempty_vector` duplicating four `owns` clauses; every
`fold` re-proving body facts a store could not have disturbed.

### B1. Modules and imports (do this first)

`import "path/to/file.click";` at file top, path-relative to the importing
file, with the stdlib promoted from a single prelude to a directory of
importable modules. Semantics kept minimal:

- Imports contribute predicates, pure functions, theorems, and resource
  definitions; a flat namespace with duplicate-definition errors (no
  renaming/aliasing in v1).
- Cycles rejected; each file elaborated once per session, cached by content.
- `verifying` declarations do not cross module boundaries — an imported file
  is a pure spec library.

This is the cheapest proposal per unit of pain: it immediately deletes the
copy-pasted lemma blocks, and nothing else (shared resource definitions for
json-c, a real lemma library, factsets below) can land without it.

### B2. Named fact-sets (spec-level abbreviation)

A hygienic, parameterized bundle of propositions usable wherever a fact list
appears (`step using`, `requires`, loop invariants, `advance` restatements):

```click
factset vector_frame(owner: int32*) {
    separate(memory(owner[0..4]), memory(load_int32_pointer(owner + 2)[0..cap]));
    loadable(owner[0..4]);
    ...
}

step using {
    facts vector_frame(owner);
    fact len == old(len);
}
```

A factset is *textual expansion during elaboration* — not a predicate, no
fold/unfold, no proof obligations of its own, no opacity. That distinction
matters: predicates answer "what is true"; factsets answer "stop making me
retype these twenty lines." The four near-identical blocks in vector.click
collapse to one definition plus four one-line uses.

### B3. Parameterized resource states

Replace state-per-resource duplication (`empty_vector` vs `nonempty_vector`)
with value-indexed resources:

```click
resource vector(owner: int32*, len: int32) {
    owns owner[0..4];
    owns data[0..cap];
    fact 0 <= len and len <= cap;
    ...
}
```

`vector(owner, 0)` and `vector(owner, n)` are then the same definition, and
state transitions become parameter changes at `fold` time rather than
cross-resource conversions. Requires fold/unfold matching up to spec-value
parameters, which reuses the A1 normalization matcher. For json-c (an object
with ~8 invariant fields and fresh/shared/frozen states) this is the
difference between linear and quadratic spec growth.

### B4. Fold-modulo-frame (a frame rule for composite bodies)

Today every `fold` requires manually re-`have`-ing each body fact, even ones
whose footprint the intervening code provably never touched
(mdtests/composite_resource_owned_buffer_set.md needs four `have ... by
{ simp(); }` lines after a single-cell store). Proposal: at `unfold`, record
each body fact's memory footprint (the kernel already computes footprints
for effects/framing); at `fold`, auto-discharge every fact whose footprint
is disjoint from the accumulated write effect since the unfold; require
explicit re-establishment only for touched facts. The certificate records
which facts were frame-discharged, so replay is still explicit. This is the
kernel-heavy proposal in this group, and the highest-leverage one for real
libraries.

### B5. Opt-in unfold/fold search in `auto`

`by auto` currently does no predicate unfolding or witness search, so
trivial contract proofs still need scripts. Allow bounded unfold/fold search
for predicates explicitly marked (e.g. `predicate sorted(...) auto;` or a
contract-level `auto using sorted, sorted_range;`). Opt-in keeps replay
predictable and search bounded; a successful search plans an ordinary
certificate (the existing smart/simple boundary handles this today).

Suggested order: B1 → B2 → B3 → B4 (B5 anytime). B1 and B2 are elaboration-
only changes; B3 and B4 touch the kernel's resource machinery.

---

## Problem C: Three overlapping concept families for memory access

`loadable(...)` (bounds), `views/owns/consumes/produces` (authority), and
`mutable/immutable` effects (write footprint) are all range-over-pointer
clauses; docs say owned resources imply loadability yet mdtests routinely
state both (mdtests/fill3_memory_postconditions.md has `requires loadable(p, 12);
consumes p[0..3];`); `loadable(p, 12)` counts bytes while every other range
counts elements; `owns X` and `consumes X; produces X` are two spellings of
one contract; `mutable_field` is load-bearing in examples but essentially
undocumented.

### C1. Permissions become the single source of authority

Target end state: the resource verbs are the one family users must learn.

- `views X` ⇒ readable/loadable; `owns X` ⇒ readable + writable;
  `loadable(...)` in a contract becomes *derived* — stated only for
  footprints not covered by any verb, and the verifier warns when a stated
  `loadable`/`separate` is already implied by the verbs (making the docs'
  existing claim actually true, and teaching users the implication via the
  warning).
- Effects clauses become optional refinements: the default write footprint
  is the owned ranges; `mutable X` only *narrows* it. A function with `owns
  p[0..n]` and no effects clauses means "may write anywhere it owns."

Migration is doc + lint first (warn on redundancy), mdtest cleanup second,
hard removal only after the corpus is clean.

### C2. One range syntax, element units only

Deprecate the byte-counting `loadable(p, 12)` form. Standardize element
ranges `p[lo..hi]` everywhere; byte width is derived from the pointer's
element type, as the resource verbs already do. Ship the migration as a
mechanical rewriter pass (the expansion machinery can do source-preserving
rewrites) plus a same-change docs update. This must land **before** uint32 /
size_t / additional widths arrive, or every spec written in the interim is a
latent unit bug.

### C3. Collapse synonym spellings

- `owns X` is canonical; lint `consumes X; produces X` with identical ranges
  into `owns X`.
- `mutable_field(p->f)` either gets first-class documentation in the Effects
  section of click-language.md, or better, is folded into the ordinary range
  grammar so `mutable p->f` is just an effects clause over a field-place
  range — one grammar for places, everywhere.
- Fix the residual doc churn while in there ("legacy spelling for
  `execute_rest()`" self-reference; `close_invariants()` missing from the
  tactic inventory).

### C4. One separation rule, stated once

Whether `separate(...)` must be written currently depends on which verb
family the author happened to use. Rule to converge on: **all owned/viewed
ranges contribute to one canonical disjointness context; explicit
`separate` is needed only between raw pointer parameters that no verb
covers.** Implement whatever small unification that requires, then document
it as a single table (verb → implies loadable? → implies separate? →
implies write?). That table replaces roughly three scattered doc sections.

---

## Cross-cutting sequencing

| Order | Item | Why first |
|---|---|---|
| 1 | A2 (names not positions), C2 (element units) | Cheap, stops ongoing damage to every new spec written |
| 2 | B1 (imports) | Unblocks stdlib growth and shared resources; everything in B depends on it |
| 3 | A3 (two-phase closers), C3 (synonym collapse) | Small, self-contained ergonomics wins |
| 4 | A1 (normalization matching) | Deep but reusable: B3 and C1 lean on it |
| 5 | B2 (factsets), C1/C4 (authority unification) | Elaboration-layer; C1 is mostly lint + migration |
| 6 | B4 (fold-modulo-frame), B3 (parameterized states) | Kernel investments; do before the json-c pilot so it doesn't fossilize current idioms |

The theme across all three problems: the kernel architecture (certificates,
smart/simple split, footprint tracking) already contains the machinery each
fix needs — these are surface- and elaboration-layer designs that expose
existing kernel capabilities, not new logic.
