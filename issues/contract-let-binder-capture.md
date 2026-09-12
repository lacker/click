# Preserve lexical aliases under quantifier binders

P1: clause-level `let` expansion captures free variables and accepts false
theorems. Reproduced at `3ad0d2e1` with explicit simple tactics.

## Violated invariant

A lexical alias denotes its initializer in the environment where it was
defined. Introducing or alpha-renaming a later binder must not change the
alias's value or change a false proposition into a true one.

`apply_contract_let_expressions_to_proposition` in
`src/surface/lowering/contract_substitution.rs` removes aliases whose names
equal a quantifier binder, then applies the remaining aliases inside its
body. It does not freshen binders that occur free in alias initializers.
`apply_contract_lets_to_expression` substitutes untyped aliases and inserts
retained typed aliases inside the body; both paths can capture variables.
The general substitution route already has
`prepare_click_proposition_binding_body`, but this special alias-expansion
route bypasses its capture avoidance.

## Status and implementation direction

The lexical-scoping behavior is the intended behavior. This issue needs an
implementation of that behavior, including preservation of existing proof
syntax and independently checkable expansion. It does not call for banning
shadowing, changing C identifiers, or introducing a new scoping rule.

An uncommitted implementation was paused after architectural review. It used
fresh surface binder keys plus `ContractExpression::Resolved { source,
expression }`, which duplicated expressions into a printing tree and a
checking tree. Do not resume that implementation as the default solution.
The recommended replacement is to retain aliases with their declaration
scope until lowering, resolve names at an explicit boundary, and preserve
the source-name correspondence in proof presentation. This is a proposed
architecture, not a verified replacement patch.

Before distributing broad implementation, one owner must demonstrate the
approach through verification, proof introduction/instantiation, and checked
expansion. The chunks below distinguish that prerequisite from work that can
subsequently proceed in parallel.

## Small reproduction

Save this as `capture.click`; no C input is needed:

```click
theorem wrong(x: int32) {
    let saved = x;
    ensures forall (x: int32) { saved == x } by {
        intro();
        normalize();
    }
}
```

`click verify capture.click` exits 0. For outer `x = 0`, `saved` must remain
0, while the inner universal quantifier includes 1, so the theorem is false.
Substitution instead changes the body into the tautology `x == x`.

Rename only the inner binder and its reference to `z`:

```click
ensures forall (z: int32) { saved == z } by {
    intro();
    normalize();
}
```

The alpha-equivalent theorem now correctly fails at `normalize`. Replacing
the outer and inner types with `Integer` and writing
`let saved: Integer = x;` reproduces the same unsound acceptance.

The existential path also accepts an impossible claim:

```click
theorem wrong(x: Integer) {
    requires x == 0;
    let saved: Integer = x;
    ensures exists (x: Integer) { saved == 1 } by {
        witness(x = 1);
        normalize();
    }
}
```

This exits 0 even though `saved` is fixed at 0 by the outer requirement.

## What the investigation established

### Capture avoidance alone loses proof names

The general `prepare_click_proposition_binding_body` substitution helper
already avoids capture by freshening binders. Applying it directly to this
special alias route also changes the names that proof scripts use after
`intro()` and in `witness(x = ...)`. A smaller fix can reuse its hygiene
logic, but must retain a correspondence between the written binder and the
binding actually checked. Freshening alone is an incomplete fix.

### C lookup can recapture a correctly elaborated alias

In `src/kernel/spec.rs`, lowering a C universal or existential installs the
quantified value into `CState.locals` under `SpecProposition`'s `name`.
Some `SpecExpression::CExpression` references are evaluated later against
that state. If an inner binder is still installed under the outer C name
`x`, a deferred reference to the outer object can be captured even when the
surface pass appeared hygienic.

Mathematical `Integer` expressions resolve to kernel variables earlier, so
an Integer-only regression does not cover this problem. Both paths must be
tested. Private binder identity must survive every deferred C lookup; a
display name is insufficient as a lookup key.

### The paused two-tree representation has no general correspondence invariant

Ordinary substitution in the prototype can change `expression` while
cloning `source` unchanged. Witness substitution has another failure mode:
its source pass substitutes into atom expressions, but the enclosing
quantifier's capture check examines the private semantic name rather than
the printed name. Source and semantics can therefore disagree after
instantiation.

For example, start with an outer parameter `x`, `let saved: Integer = x`,
and the claim:

```click
exists (z: Integer) { forall (x: Integer) { z <= saved } }
```

After `witness(z = x)`, the inserted value is the outer parameter. A residual
source formula `forall (x: Integer) { x <= saved }` instead refers to the
inner variable. Preserving the original spelling of each atom does not
preserve its scope. Reification must consider the surrounding proposition
and the current proof scope together.

This is a static finding in the prototype's substitution paths, not a claim
that a particular final expanded file has been reproduced failing. Some
passing arithmetic regressions avoid serializing the problematic residual
expression by emitting a canonical constant or premise-derived certificate.
They do not establish a general correspondence between the two trees.

### Some prototype changes compensated for the representation

The prototype added a clause alias registry to support alias names in
explicit proof inputs. That made retained source spellings printable, but
also extended alias visibility beyond its previous implementation. The
capture fix must not silently depend on introducing additional proof syntax
or visibility rules.

It also changed post-execution existential expansion and the following
tactic dispatch. The original `outcome_existence_surface_certificate`
deliberately emitted `have full_exists by { completed proof }; assumption`.
Repeating a witness or introduction inside that independently checked
`have` is intentional reproof, not evidence of a preexisting bug. Those
changes are not established prerequisites for this issue.

The previous focused tests are useful evidence about individual examples.
The complete `scripts/check.sh` gate never passed for that prototype. Treat
its regression examples as investigation material, not its representation
or adjacent changes as a foundation that must be preserved.

## Proposed architecture and its invariants

### 1. Retain declaration scope instead of expanding under a later binder

Keep each value alias's initializer, optional type annotation, and lexical
definition context until proposition lowering. A clause must identify the
alias declarations visible at that point in the declaration sequence.
An alias initializer may refer to earlier aliases and surrounding declared
parameters; it must not see subsequent aliases or quantifiers introduced
inside a later clause.

Use a shared immutable declaration table or persistent lexical environment
with indexed lookup. A clause can hold a scope handle or visibility prefix;
it should not clone all previous declarations. The exact Rust types are for
the initial implementation to establish. Their required behavior is:

- Lookup an alias by identity/name in the clause's lexical scope.
- Resolve its initializer in the scope at its definition, recursively using
  earlier alias definitions when needed.
- Extend the use-site scope for a quantifier without changing the scope in
  which an already-declared alias's initializer is resolved.
- Preserve existing duplicate-declaration diagnostics and distinct
  namespaces for values, resources, types, and definitions.
- Preserve typed/untyped inference and evaluate only dependencies actually
  needed by the selected expression. An unused abbreviation must not become
  an eagerly evaluated expression with new obligations.

Apply this to requirements as well as ensures. Audit function contracts,
pure theorems, structural clauses, resource arguments, and memory segments;
keeping scope only on `EnsureClause` leaves other entry points exposed.
Audit parser preprocessing too: alias initializers are currently rewritten
against preceding declarations before clauses are lowered.

`let ... where` introduces a checked witness; it is not an ordinary value
alias. Preserve its existing existential/obligation behavior and the scopes
of value aliases before and after it. Never turn an unchecked `where`
declaration into a freely available value.

### 2. Separate lexical binding from the C state being observed

An alias is an abbreviation, not a declaration-time runtime snapshot.
Keeping the declaration environment means retaining which variable a name
denotes. It must not freeze the variable's value at function entry.

For example, with fixed C source:

```c
int32 check(int32 x) { x = x + 1; return x; }
```

a contract alias `let saved = x;` must keep denoting that C variable.
Current-state uses, `old(saved)`, and `at(function.entry, saved)` must retain
the existing selection of state. An inner quantifier named `x` must not
change the identity of the C variable in any of those expressions.

Conceptually, alias lowering takes two separate inputs: a lexical scope
and the selected evaluation state/memory. Do not cache an evaluated alias
value using only the alias's declaration identity. State-dependent work
must remain state-dependent, and caches must distinguish actual semantic
contexts without hashing or comparing complete environments.

### 3. Resolve checking identities at a narrow boundary

Keep the parsed source expression as syntax. Lower it through its lexical
scope into one semantic representation. Existing `SpecExpression` and
kernel variable identities should be reused where sufficient. Avoid adding
a pair of mutable source/semantic expression trees throughout the surface
AST or a general family of modes to keep those trees synchronized.

Allocate private identities for bound variables during lowering. For C
binders, every path that emits a deferred C reference must preserve that
identity. Installing the quantified value must not overwrite the lookup
key for an unrelated C object or outer binding. Audit C fragments as well
as Click-native expression nodes, including casts, pointer expressions,
arrays, segments, snapshots, and range bounds/bodies.

It is not yet established that this requires semantic IDs throughout
`ClickProposition`. Start by locating them at elaboration and proof
presentation boundaries. If the initial implementation needs an additional
resolved reference form, specify its invariant and consumers before
expanding it across the AST. Retained source syntax is provenance; it must
not independently become the authority for emitted certificates.

### 4. Resolve proof inputs once and preserve written binder names

`intro()` still makes the written quantifier name available in the proof
scope. `witness(x = value)` still selects the written existential binder.
Its value is resolved in the surrounding scope before removing that
binder; it must not accidentally refer to the existential being solved.
Instantiating the existential leaves the surrounding source-name scope
unchanged: `witness` does not introduce a proof-local alias or replace an
existing binding. In particular, `witness(x = x + 1)` must not change what a
subsequent proof input named `x` denotes. A witness name absent from the
surrounding scope does not become a new usable proof-local name afterward.

Use the existing proposition/proof presentation machinery to retain the
written name and the exact checked variable together. Parsed proof inputs
may perform source-name lookup through that scope. Already resolved goals
must be instantiated by binding identity rather than having source-name
substitutions repeatedly applied to them.

The scope must be branch-local and nest correctly through `have`, logical
splits, nested introductions, and existential witness instantiation. Handle pure,
fixed-state, and execution proof contexts; correctness in only one driver
is insufficient. Predicate/theorem application must distinguish formal
parameter substitution from lookup of a proof-local source name.

Preserve established proof-input visibility. If correct expansion needs
new availability of clause aliases in proof inputs, identify that need in
the initial implementation and record the precise behavior and justification
here before distributing downstream work. Do not introduce it accidentally
as a printer workaround, or silently change what a witness step binds.

### 5. Reify generated proofs from identities and the active source scope

Printing a resolved expression means choosing source syntax that resolves
back to the same expression in the scope where the generated step will
appear. A cached original spelling is not sufficient after substitution.

If a generated quantifier would capture a free reference, freshen that
generated binder and consistently update references within its generated
scope. Preserve the names and meaning of the user's existing proof steps.
Freshening a generated binder does not by itself make a hidden outer
variable name usable in an existing proof scope; the initial implementation
must demonstrate that case using supported source constructs too.

The required round-trip property is: reparse and lower the emitted proof
input in its actual context, and obtain the same checked proposition or
term, allowing alpha-equivalence of bound variables. Check its certificate
independently against the original source claim. Do not compare independently
allocated variable numbers as though they were stable source identities.

Exercise a path that really emits a formula containing the instantiated
outer variable. A constant arithmetic certificate that avoids printing the
formula is useful additional coverage, not the sole test of this invariant.
Include ordinary formal substitution and quantified enumeration as well as
witness substitution: each can remove a binder or change what a source
name would denote.

## Implementation chunks

The coordinator owns the shared interface and integration order. These are
bounded work packages for subagents, not permission to implement competing
representations in parallel. File names below are entry points; check the
current base before editing because other repository work is active.

### Chunk 0: Baseline, regressions, and a complete small implementation

**Owner:** coordinator/one implementation agent. A separate regression agent
can prepare black-box fixtures concurrently. **Dependencies:** none.

1. Start a clean task worktree from the agreed integration base. Preserve
   the paused prototype separately. Record baseline verifier/expansion
   behavior and any unrelated gate failures; do not import its diff wholesale.
2. Establish the failing universal and existential examples above and true
   controls, with both shadowing and alpha-renamed binders. Use existing
   verifier/expansion test helpers. Red regressions stay in the task worktree
   until a fixing implementation makes them green.
3. Implement the smallest complete path using retained declaration scope:
   parsing/storage, lowering, proof introduction/witness, and reification.
   Include both Integer and deferred C lookup. The nested outer-witness
   example must exercise actual source reification, not only trivial closure.
4. Check that written proof names survive, old/current state behavior is
   preserved, and generated explicit proofs independently verify.
5. Record the chosen scope carrier, identity allocation, proof-input
   resolution boundary, and reification interface in this issue. Name each
   caller that must adopt them and resolve ownership of shared files.

**Deliverable:** a reviewed small implementation plus concrete interface
contracts for the following chunks. The proposed architecture must earn
confidence here; a successful false-theorem rejection alone is insufficient.
If it cannot handle nested witness expansion without another sweeping
representation or new language behavior, reduce and report that exact
obstacle before broadening the patch.

### Chunk 1: Scope storage and declaration plumbing

**Owner:** surface/parser agent. **Dependencies:** Chunk 0 interfaces.

**Entry points:** `src/surface.rs`, `src/surface/parser.rs`,
`src/surface/lowering/contract_substitution.rs`; a dedicated scope module
only if the agreed design needs one.

- Replace the unsafe eager clause-alias expansion with the agreed scope
  carrier. Retain the original declaration order and initializer scopes.
- Wire requirements, ensures, aggregate clause splitting, structural
  clauses, theorem and function blocks to the appropriate scope.
- Keep scopes shared and immutable. Use indexed identity/dependency lookup;
  do not copy a declaration prefix for every clause or alias use.
- Preserve error behavior for duplicate names and invalid declarations.
  Preserve `let ... where` checking and dependency boundaries.
- Coordinate AST definition edits with the coordinator instead of forcing
  proof and lowering agents to invent parallel fields or constructors.

**Acceptance:** focused scope tests cover earlier/later declaration visibility,
alias chains, unused aliases, independent clause scopes, shadowing of an
alias name versus a free name in its initializer, and `where` interactions.
Provide the lowering/consumer agents with stable scope APIs and examples.

### Chunk 2: Hygienic lowering and deferred C references

**Owner:** lowering agent. **Dependencies:** Chunk 0; uses Chunk 1 APIs.

**Entry points:** `src/surface/lowering/annotations.rs`,
`contract_environment.rs`, `resource_lowering.rs`; audit
`src/kernel/primitives.rs` and `src/kernel/spec.rs` where lookup is deferred.

- Lower alias initializers with the definition scope and the selected C
  state, preserving annotation/inference behavior for C and Integer values.
- Give quantified values lookup identities that cannot overwrite outer
  bindings. Keep source names available to the proof presentation layer.
- Cover `forall`, `exists`, `.all`, and `.any`. Range start/end expressions
  are outside the range item binder's scope; its body is inside that scope.
- Cover pointers, memory segment base/start/end, resource arguments, and
  C fragments that bypass ordinary expression decomposition.
- Verify current, `old`, and `at` evaluation without freezing aliases at
  declaration time. Reuse kernel binding identities where available.
- Keep certificate validation and proof rules unchanged unless a precise
  representation requirement is established; document any kernel change.

**Acceptance:** false capture examples reject and corresponding true examples
verify for Integer and C types. A C regression demonstrably reaches deferred
lookup, and a mutation/snapshot regression distinguishes lexical binding
from entry-state values. Return exact checked binder identities to Chunk 3.

### Chunk 3: Proof binding scopes and source reification

**Owner:** proof agent. **Dependencies:** Chunk 0; Chunk 2 identity contract.

**Entry points:** `src/surface/proof/surface_lowering.rs`,
`proof_object/step_application.rs`, `proof_object/fixed_state_steps.rs`,
`pure_theorems.rs`, `cursor_execution.rs`, `surface_certificates.rs`,
`smart_closures.rs`, and `src/surface/printing.rs`.

- Map introduced written names to the exact checked variables. Resolve
  parsed proof operands through that map without rewriting resolved goals
  by source name. Keep nested scopes and sibling branches independent.
- Resolve witness operands in the surrounding scope; instantiate by
  identity; preserve subsequent written names for remaining binders and
  leave the surrounding proof-local bindings unchanged.
- Reify generated expressions with capture avoidance over the enclosing
  proposition and live proof scope. Cover witnesses, instantiated theorem
  or predicate formals, and finite quantified enumeration.
- Check pure, fixed-state, and post-execution proofs, including nested
  `have` and logical branches. Do not rely on only one proof driver's maps.
- Preserve the established existential expansion strategy unless an
  independently reproduced defect requires changing it. Repeating a
  completed proof inside a new checked `have` is not itself a bug.

**Acceptance:** existing `intro`/`witness` scripts retain meaning; expanded
proofs reparse and independently verify the original claims. Include
nontrivial output that exposes a captured outer reference if printing is
wrong. No private lookup keys leak into source or normal diagnostics, and
no expression is printed solely from stale provenance.

Include a witness-scope regression with outer `x == 0`, an existential also
named `x`, and `witness(x = x + 1)`. The subsequent explicit proof input
`have x == 0 by { assumption(); }` must still refer to the outer parameter.
Also test a witness name with no previous surrounding binding; instantiating
it must not create a proof local. Complete the enclosing true claims with
established simple tactics and verify their expansions.

### Chunk 4: Other scope consumers and compatibility

**Owner:** consumer-audit agent, or the scope agent after Chunk 1.
**Dependencies:** scope API and lowering boundary from Chunks 0–2.

**Entry points:** `src/surface/generics.rs`,
`validation/declaration_expansion.rs`, `validation/type_validation.rs`,
`validation/algebraic_types.rs`, `validation/definition_validation.rs`,
`validation/expression_analysis.rs`, `proof/theorem_application.rs`, and
the remaining alias/substitution callers found by repository search.

- Audit consumers that previously received already-expanded aliases.
  Make them scope-aware where needed without adding a second independent
  alias evaluator with different binding rules.
- Preserve generic instantiation, resource-instance renaming, predicate
  substitution, and contextual literal/type inference. An alias RHS must
  receive the appropriate formal substitutions without entering an inner
  binder's use-site scope.
- Transform shared scope tables once per relevant instantiation operation,
  or use an equivalent shared representation. Do not repeatedly deep-clone
  the same table for every clause.
- Preserve distinctions between value binding identity, resource identity,
  and source spelling. Audit snapshots and diagnostic formatting too.

**Acceptance:** relevant existing syntax/type/generic/resource regressions
remain green; new integration tests instantiate alias-bearing declarations
under shadowing binders. Retain the original source in compatibility tests.

### Chunk 5: Adversarial regressions and deterministic scaling

**Owner:** regression agent. **Dependencies:** prepare baseline cases during
Chunk 0; integrate against the agreed interfaces and working implementation.

**Entry points:** focused surface tests, existing expansion helpers,
`src/instrumentation.rs`, and existing deterministic-work regressions.

Use the matrix below to choose small, independent cases. Port black-box
examples from the paused prototype selectively; do not port assertions
that require `Resolved`, `@binding` as an implementation format, or a new
alias-in-proof visibility rule. Checks for leaked private names should use
the actual chosen representation.

Protect approximately linear work with deterministic counters at multiple
sizes, for example 32, 64, 128, and 256. Include:

- Many unrelated alias declarations with a fixed-size selected use.
- Long shared alias dependency chains used by multiple clauses; retained
  dependencies must not be repeatedly expanded into exponentially large trees.
- Increasing binder depth and independent expression-local lets during
  substitution/resolution, including capture checks.
- Repeated simple proof steps with growing unrelated ambient bindings.
- Generic/resource transformation of a shared declaration scope.

Also detect quadratic dependency traversal: use `n` trivial Integer aliases
(`a0 = x; a1 = a0; ...`) and `n` constant-size claims about the final alias in
one unchanged context. Both the source and resolved values are linear in
total size. Walking or rebuilding the entire chain for every claim costs
quadratic work and fails the contract even without exponential expansion.
Require shared resolution/indexed reuse, while respecting the separation
between lexical identity and state-dependent values described above.

Count actual visited/resolved/cloned work, not only top-level API calls.
Charge unavoidable emitted syntax to output size. Keep existing scaling
thresholds; a newly exposed performance defect needs a reduced explanation
and an appropriate fix, not a larger allowance. A fast fixed example or a
warm run does not establish the required complexity.

**Acceptance:** black-box verification and expansion agree, negative tests
fail for the intended proof reason, and deterministic curves comply with
[verification-efficiency.md](../docs/internals/verification-efficiency.md).

### Chunk 6: Integration, documentation, and closure

**Owner:** coordinator. **Dependencies:** all preceding chunks.

- Review the combined diff against the scope of this issue. Remove
  abandoned two-tree plumbing and changes that only compensate for it.
  Keep unrelated expansion or performance changes separate unless their
  necessity has been demonstrated on the chosen implementation.
- Document lexical alias scope in `docs/concepts/contracts.md`, including
  the distinction from a runtime snapshot and the existing proof-name
  behavior. Document additional public behavior only if deliberately adopted.
- Run focused regressions, then the complete `scripts/check.sh` in the task
  worktree. Judge the full gate by its unpiped exit status. Focused runs
  should use the gate's stack setting (`RUST_MIN_STACK=8388608`) and bounded
  nextest configuration. Do not treat `cargo test --lib` as the gate.
- If a bounded run is interrupted or times out, confirm its verifier process
  tree exited. Follow `AGENTS.md` when a tooling failure blocks progress;
  do not increase budgets, hide the original source, or accept an
  unverifiable expansion as a temporary success.
- Integrate only a coherent green commit. Recheck the primary checkout and
  agreed base; if upstream moved, update the task branch and rerun affected
  gates. Never copy partially implemented files into the primary checkout.
- Delete this issue and its existing README entry when the fix, regression
  coverage, and documentation land together.

## Regression matrix and final acceptance

Each semantic dimension needs a true control as well as a false claim where
applicable. Test alpha-renamed pairs: renaming only a bound variable and its
bound occurrences must not change the verifier's answer. Negative soundness
tests for otherwise well-formed claims must parse and elaborate successfully,
then fail proof checking; an unknown name or type error is not evidence that
capture was fixed. Separate invalid-scope/type tests should retain their
intended elaboration errors.

| Dimension | Required observations |
| --- | --- |
| Quantifiers | `forall` and `exists`, including unused binders and repeated written names. |
| Ranges | `.all` and `.any`; bounds use outer scope, bodies use item scope. |
| Alias forms | Typed/untyped aliases, dependencies, unused aliases, alias-name shadowing, and initializer-free-name shadowing. |
| Clause order | Requirements and claims have their own visibility; later aliases never leak backward. |
| Witness aliases | Value aliases before/after `let ... where`; unchecked witnesses are never materialized as definitions. |
| Types/state | Integer, C integers, pointers, mutable C parameters, current/old/recorded state. |
| Other consumers | Predicate/theorem substitution, generics, resources, memory segments, and contextual type inference. |
| Proof scope | `intro`, `witness`, nested quantifiers, branches, nested `have`, and all applicable proof drivers. |
| Reification | Outer witness beneath a shadowing binder, removed quantified binders, and substituted formal parameters actually appear in emitted source. |
| Expansion | Ordinary verification succeeds first; expansion reparses and independently verifies the unchanged original claim. |
| Scaling | Indexed shared scopes, output-sensitive dependency handling, and deterministic multi-size regressions. |

Final acceptance also requires the exact false theorems in this issue to be
rejected, legal shadowing and existing proof syntax to remain supported,
original C sources to remain unchanged, and `scripts/check.sh` to pass.

## Delegation and worktree protocol

Run Chunk 0 before assigning the representation-dependent chunks. During it,
other agents can independently prepare regressions or audit callers. After
its interfaces are settled, scope plumbing, lowering, and proof integration
can proceed in parallel in separate task worktrees; schedule the consumer
audit and final regression work as slots free up.

Each assignment must include the agreed base commit, interface contracts,
owned files, dependencies, expected regressions, and the prohibition on
continuing the paused representation by default. Shared files such as
`src/surface.rs` need one designated editor/coordinator. Do not have agents
concurrently mutate the same prototype worktree.

Require each handoff to state what changed, what remains unproved, exact test
commands and exit statuses, and whether the full gate passed. A focused
green run is not a full-gate result. Do not commit failing prototypes or
integrate incomplete capture fixes merely to make parallel handoffs easier.
Subagents should report unresolved design questions to the coordinator with
a concrete example, rather than silently choosing new language behavior.

Optional local investigation material, if those worktrees still exist:
`/private/tmp/click-lexical-alias-bindings` on
`codex/lexical-alias-bindings` contains the paused prototype and regression
examples; its base was `31e6366e`. This issue is intended to stand alone if
that uncommitted material is unavailable. Use the reproductions and
invariants above as the requirements, not the prototype's implementation.
