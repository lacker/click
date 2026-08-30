# Tactic taxonomy and reference audit

The nonsemantic taxonomy and reference cleanup from this audit is complete.
The simple, smart, and control definitions now agree; intrinsic tactic class
is distinct from source-site ownership of omitted automation; the tactic table
is checked row by row; and the affected reference entries have focused positive
coverage. One semantic question remains: the boundary of `assumption()`.

## Violated invariants

- Every public tactic has one accurate description of its checked behavior.
- A simple tactic requests one deterministic checked operation without
  heuristic planning or search, and its checking work is fast and
  output-sensitive.
- A smart tactic that succeeds can expand into ordinary surface-expressible
  simple tactics whose rewritten source verifies normally.
- Control forms remain structural containers; attributing omitted or nested
  automation to a source location does not change the container's intrinsic
  tactic class.
- Documentation coverage associates each registered form with its own class,
  description, and genuinely checked positive use.

## Audit findings

### The definition of simple is inconsistent (resolved)

The tactic reference says that a simple tactic operates from explicitly named
data. That excludes `step()`, which deterministically checks one selected C
transition while consulting the current indexed fact and resource context. It
also poorly describes `extract(P)`, which performs bounded structural
derivation. Other concept and internal pages variously say "explicit rule",
"explicit evidence", or merely "bounded".

The intended definition is: a simple tactic requests one deterministic checked
operation and performs no heuristic planning, premise selection,
alternative-rule search, or speculative proof branching. It must be fast:
work may scale with explicit input, the affected program operation, indexed
access to current proof context, and the proof-state delta it produces, but not
with unrelated ambient state. Expansion should remove essentially all
conveniently avoidable planning and search cost while retaining the unavoidable
cost of checking the emitted operations.

`docs/concepts/proof-scripts.md` also directly contradicts itself by listing
`step()` as smart and later describing it as both simple and "one smart
transition".

### `assumption()` is more permissive than its reference entry (open)

The reference says `assumption()` performs exact lookup. Depending on proof
context, the kernel also accepts an alpha-equivalent quantified fact, a
context-free normalization, a discharged implication consequent, or an exact
fact modulo condition polarity and certified resource-separation identity.
Normalization and implication discharge overlap `normalize()` and `extract()`;
the other equivalences can reasonably be part of semantic fact identity.

Alpha-equivalent quantified facts are different in kind: binder identity is an
internal representation detail. Accepting alpha-equivalence is compatible with
an "exact semantic fact" contract even though structural set lookup misses it.

#### Corpus diagnostic

`assumption()` has 584 checked source occurrences across 33 mdtest, example,
and surface-test files (including generated test-source strings). A throwaway
kernel switch independently removed each convenience while running the
ordinary fixture and unit gates:

- removing quantified equivalence breaks two of 411 mdtests; retaining it while
  removing all other conveniences makes all 411 pass;
- removing condition-polarity/resource-separation matching breaks one of 1,213
  library tests, where checked outcome `simp` depends on the polarity-equivalent
  loop-exit bound;
- removing discharged implication extraction leaves all 1,213 library tests,
  all mdtests, and all examples green;
- removing context-free normalization breaks five library tests (three direct
  proof patterns plus two duplicate example-pipeline checks) and at least two
  examples, `bounded-pool` and `owned-string`. These sites use `assumption()`
  to prove a proposition from the current symbolic state rather than reuse a
  stored fact, so `normalize()` is the natural explicit operation.

The diagnostic switch lives only in a throwaway worktree and is not part of
the proposed change.

#### Design options

1. Keep the implementation and broaden the documentation. This avoids proof
   migration, but leaves one lookup tactic overlapping three explicit proof
   operations and changing meaning by context.
2. Make `assumption()` exact semantic lookup: accept an available fact modulo
   alpha-renaming, condition polarity, and certified resource-separation
   identity, but require `normalize()` for symbolic evaluation and `extract()`
   for implication discharge. This is the preferred boundary. The known
   normalization sites require a small proof migration; no C changes are
   needed.
3. Require structural identity only. This exposes binder and lowering details
   to proofs and already breaks two mdtests.
4. Preserve the broad operation under a second tactic name while narrowing
   `assumption()`. The corpus evidence does not currently justify another
   public tactic.

### A second source-site classification obscures intrinsic tactic class (resolved)

`ProofTactic::class()` gives each AST form an intrinsic simple, smart, or
control class. `source_tactic_class()` separately reclassifies source
occurrences for profiling and expansion:

- `have` may be reported as simple, smart, or control based on its body;
- `loop` becomes a smart source site when phase or effect proofs are omitted.

The reference explains the `have` exception but not the analogous `loop`
behavior. Containers should remain intrinsically control. The separate concept
should be named for what it does, such as an *expandable source site* or
*automation source anchor*, rather than being another tactic class.

### Several reference descriptions are incomplete or too strict (resolved)

- `cases` also works at an execution frontier: each branch retains the same
  checked C state, receives its exact disjunct, and checks subsequent execution
  separately. The public row describes only proposition reasoning.
- `contradiction(P)` can accept a negation that normalizes context-free to true,
  despite its exact-facts description.
- `left()` and `right()` accept canonical condition-polarity equivalents as
  well as structurally identical facts.
- Predicate `unfold(name)`, pure-function `unfold(function(args))`, and
  resource `unfold(resource(args))` are separate registered forms with
  different transitions; their reference entries must remain distinct.

The resource-operation descriptions themselves are otherwise accurate:
`observe` projects a non-consuming declared view while retaining the folded
resource, `unfold` exposes one body layer, `fold` consumes the body to recreate
the named resource, and `open` scopes an unfold/fold transition.

### The mechanically checked documentation coverage is weaker than advertised (resolved)

The form-inventory test checks that each syntax string and class word occurs
somewhere on the complete reference page. It does not associate the registered
class with the corresponding Markdown row, so a wrongly classified row can
remain green.

The positive-fixture inventory checks that a source file contains a needle and
that the file belongs to an ordinary test suite. Some needles, including
`open(` and `) using {`, are too generic to establish that the intended form is
still the checked use. The test does not structurally associate a Rust source
occurrence with the particular `#[test]` that verifies it.

## Remaining intended regressions

1. `assumption()` closes a goal from a semantically identical available fact,
   including alpha-equivalent quantified binders.
2. `assumption()` does not normalize an otherwise unavailable proposition;
   `normalize()` proves the same goal.
3. `assumption()` does not extract a discharged implication consequent;
   `extract()` makes it available explicitly.
4. `assumption()` accepts condition-polarity and certified
   resource-separation identity, but does not derive an otherwise unavailable
   mutable fact across an effect; `transport()` does so explicitly.
5. The migrated example and all existing tactic fixtures verify.

## Remaining acceptance criteria

- Choose and document one context-independent semantic contract for
  `assumption()`.
- The kernel implements that contract without a linear scan of unrelated
  facts.
- Focused positive and negative regressions distinguish lookup from
  normalization, extraction, and transport.
- Any affected checked proofs are migrated without changing their C.
- `scripts/check.sh` passes.
