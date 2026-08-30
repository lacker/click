# Tactic taxonomy and reference audit

The public tactic vocabulary is mostly coherent, but its implementation,
reference documentation, profiling classification, and expansion model do not
yet agree at every boundary. This issue records the complete audit so the
remaining cleanups can land independently without losing the overall design.

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

### The definition of simple is inconsistent

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

### `assumption()` is more permissive than its reference entry

The reference says `assumption()` performs exact lookup and rejects merely
derivable or differently spelled facts. Depending on proof context, the kernel
also accepts quantified-equivalent facts, context-free normalization,
discharged implication consequents, and facts available across certified
effects. This blurs the boundary among `assumption()`, `normalize()`,
`extract()`, and explicit transport.

The preferred design is for `assumption()` to perform exact semantic lookup and
for the other derivations to remain explicit, but narrowing it changes visible
proof behavior and requires a separate decision and regression review.

### A second source-site classification obscures intrinsic tactic class

`ProofTactic::class()` gives each AST form an intrinsic simple, smart, or
control class. `source_tactic_class()` separately reclassifies source
occurrences for profiling and expansion:

- `have` may be reported as simple, smart, or control based on its body;
- `loop` becomes a smart source site when phase or effect proofs are omitted.

The reference explains the `have` exception but not the analogous `loop`
behavior. Containers should remain intrinsically control. The separate concept
should be named for what it does, such as an *expandable source site* or
*automation source anchor*, rather than being another tactic class.

### Several reference descriptions are incomplete or too strict

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

### The mechanically checked documentation coverage is weaker than advertised

The form-inventory test checks that each syntax string and class word occurs
somewhere on the complete reference page. It does not associate the registered
class with the corresponding Markdown row, so a wrongly classified row can
remain green.

The positive-fixture inventory checks that a source file contains a needle and
that the file belongs to an ordinary test suite. Some needles, including
`open(` and `) using {`, are too generic to establish that the intended form is
still the checked use. The test does not structurally associate a Rust source
occurrence with the particular `#[test]` that verifies it.

## Intended regressions

1. A documentation regression rejects any normative page that classifies
   `step()` as smart.
2. Focused semantic tests pin the chosen exact behavior of `assumption()`,
   `contradiction()`, and condition-polarity disjunction introduction.
3. A reference-inventory regression associates every public form ID with the
   class in its own table row.
4. Each positive-fixture mapping uses a distinctive complete tactic spelling
   inside a test that verifies that proof.

## Acceptance criteria

- The canonical simple/smart/control definition includes the performance and
  expansion contract and is used consistently throughout public and internal
  documentation.
- `step()` is documented everywhere as a simple deterministic statement
  transition over indexed ambient context.
- `assumption()`, `contradiction()`, `left()`, and `right()` either match their
  exact documented semantics or their documentation explicitly states the
  accepted equivalences; any semantic change has focused regressions.
- `cases`, all three `unfold` forms, and omitted loop automation are described
  accurately.
- Intrinsic tactic class and source-location ownership of automation have
  distinct names and responsibilities.
- Reference and positive-fixture tests fail on a per-form class mismatch or a
  stale/non-distinctive checked use.
- `scripts/check.sh` passes.
