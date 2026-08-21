# Glossary

This glossary defines Click and theorem-proving terms for programmers. Each
definition is intentionally short; follow its links for the operational model.

## A

**Alias**
: A pointer or reference that can designate storage also designated by another
  value. Click tracks the permissions needed to reason soundly in the presence
  of aliases. See [Aliasing and frames](../concepts/aliasing-and-frames.md).

**Assumption**
: A proposition temporarily available as true in a proof context. A contract
  requirement becomes an assumption when Click verifies the function body.

**Audit**
: A whole-workflow check that discovers smart proof sites, expands them,
  verifies replay, and applies performance policy. See [Audit](../concepts/audit.md).

## B

**Binder**
: A syntax form that introduces a local name, as in `forall (x: int32)` or
  `|acc, k|`. The name is in scope only in the associated body.

**Bounded search**
: Search stopped by deterministic work budgets. Failure to find a proof within
  the budget doesn't mean that the claim is false. See [Smart and simple
  tactics](../concepts/smart-and-simple-tactics.md).

**Branch**
: One path created by a conditional or by proof case analysis. Branches carry
  path-specific facts and must satisfy the required join conditions.

## C

**C fragment**
: C syntax embedded in a Click contract or tactic to identify an expression,
  statement, or program point. A fragment is resolved against the verified C
  function; it isn't executed as a separate program.

**C0**
: Click's deliberately supported subset of C. It is the verification boundary,
  not a claim to implement every ISO C behavior. See [Supported C0](language/c0.md).

**Certificate**
: The deterministic sequence of simple proof steps produced for replay. A
  smart tactic is successful only if its certificate replays.

**Completeness**
: The ability of a proof procedure to find every true result in a stated
  domain. Click's bounded smart tactics are intentionally incomplete;
  incompleteness doesn't weaken soundness.

**Contract**
: A modular specification of a C function, including requirements, guarantees,
  effects, resources, and structural obligations. See
  [Contracts](../concepts/contracts.md).

**Control-flow tactic**
: A tactic that follows or structures C execution, such as `if`, `branch`, or
  `loop`. See [Tactics](tactics/index.md).

## D

**Definedness**
: The condition that evaluating a C or Click expression stays within Click's
  modeled rules, including arithmetic and memory rules. `defined(e)` states
  this condition explicitly.

## E

**Effect**
: A declared change to memory or an abstract resource across a function call.
  Effects delimit what modular verification may treat as changed.

**Elaboration**
: Context-dependent translation from convenient Surface Click forms into more
  explicit checked forms before kernel lowering.

**Execution path**
: One symbolic route through C control flow, paired with its path conditions
  and symbolic state.

**Expansion**
: Replacement of smart proof syntax with the simple replayable tactics in its
  certificate. See [Expansion](../concepts/expansion.md).

## F

**Fact**
: A proposition established and available in the current proof state. Facts
  can come from requirements, execution, theorem application, or earlier proof
  steps.

**Frame**
: The portion of owned state or resources that an operation doesn't consume or
  change. Frame reasoning carries that portion across the operation.

**Frontier**
: The current set of symbolic execution points represented by a proof state.
  A frontier can contain multiple paths after branching.

## G

**Goal**
: A proposition or state transition that remains to be proved. A proof is
  complete when it closes every generated goal.

## I

**Induction**
: Proof by a base case and a step that assumes the proposition for a smaller
  case. Click exposes induction where documented by the `induct` tactic.

**Instantiation**
: Substitution of a concrete term for a quantified binder. The `instantiate`
  tactic derives a particular consequence from a universal fact.

**Invariant**
: A proposition or resource condition that holds initially and is preserved by
  every loop iteration. It summarizes arbitrarily many iterations.

## J

**Join**
: The point where multiple symbolic paths are reconciled into a state suitable
  for following common control flow.

## K

**Kernel**
: The small trusted checker and semantic core that validates primitive proof
  steps. See [Kernel](../internals/kernel.md).

**Kernel Click**
: Click's internal, explicit representation after validation and lowering.
  Kernel Click has no user-facing textual syntax.

## L

**Loadability**
: Evidence that a memory access can read the required bytes at a pointer in a
  particular memory state. See [Loadability](../concepts/loadability.md).

**Lowering**
: Translation from validated Surface Click into kernel propositions, terms,
  contracts, and proof operations.

## M

**mdtest**
: A repository fixture consisting of C, Click, and expected-result sections in
  Markdown. The gate verifies mdtests with deterministic bounds.

## O

**`old`**
: A snapshot form that evaluates its subject in function-entry state rather
  than current state.

**Ownership**
: The right represented by a resource or permission to rely on, transform, or
  transfer some state. Click models ownership explicitly rather than inferring
  exclusive access from a C pointer alone.

## P

**Permission**
: Evidence authorizing a particular view or operation on state. Permissions
  support modular reasoning about reads, writes, aliases, and frames.

**Postcondition**
: A guarantee that must hold at a successful function outcome, normally written
  with `ensures`.

**Precondition**
: A fact or resource the caller must supply, normally written with `requires`.

**Premise**
: A proposition required before a theorem or reasoning rule can establish its
  conclusion.

**Profiling**
: Attribution of verifier work and elapsed time to proof sites. See
  [Profiling](../concepts/profiling.md).

**Proof**
: Evidence that every goal generated by a claim is valid under its assumptions.

**Proof mark**
: A named point in proof execution, created by `mark`, that later tactics can
  select or compare.

**Proof object**
: Structured evidence describing checked proof operations. Click's proof
  objects are replayed rather than trusted merely because search produced them.

**Proof state**
: The current goals, facts, symbolic execution frontier, resources, and
  bookkeeping needed to continue a proof.

**Proof unit**
: A selectable claim-sized unit verified and reported independently, such as a
  contract clause or theorem claim.

**Proposition**
: A statement that can be true or false and can therefore be assumed or proved.

## Q

**Quantifier**
: `forall` or `exists`, which states a proposition for every value or for at
  least one value of a type.

## R

**Replay**
: Deterministic checking of a proof certificate from its initial state. Replay
  separates heuristic proof discovery from acceptance.

**Resource**
: A logical representation of owned state with rules for transfer, splitting,
  combination, and consumption.

## S

**Sidecar**
: A `.click` file associated with existing C source. It adds specifications and
  proofs without rewriting the C. See [Files and sidecars](../concepts/sidecars.md).

**Simple tactic**
: A bounded, explicit operation whose requested proof-state transition is
  checked directly and recorded for replay.

**Smart tactic**
: A heuristic planner that searches for a sequence of simple steps. Search is
  untrusted; the resulting certificate must replay.

**Snapshot**
: An immutable reference to state at a selected proof point, used by `old`,
  `at`, marks, and memory comparisons.

**Soundness**
: The property that Click accepts only claims justified by its modeled
  semantics and trusted rules. Soundness is distinct from search completeness.

**Surface Click**
: The user-facing language parsed from `.click` files.

**Symbolic execution**
: Evaluation of C over symbolic values and path conditions so one proof can
  cover many concrete inputs.

## T

**Tactic**
: A proof-script command that requests a transition of the current proof state.

**Theorem**
: A named proposition with a checked proof that can be applied in later proofs.

**Trusted computing base**
: The implementation whose correctness is assumed when treating a successful
  Click verification as valid. Smart search is outside this boundary because
  its output is replayed by checked simple operations.

## U

**Undefined behavior**
: A C operation for which the modeled language assigns no valid program
  behavior. Click requires proofs to rule it out on verified paths.

## V

**View**
: A logical interpretation of underlying state, usually represented through a
  resource or permission and related to other views by explicit rules.

## W

**Witness**
: A concrete term supplied to prove an existential proposition. The `witness`
  tactic chooses it.

## Special forms

**`at`**
: A proposition or expression form interpreted at a selected snapshot or proof
  point rather than at the current state.
