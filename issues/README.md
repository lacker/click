# Open issues

One `.md` file per independent open problem. Each issue contains a small
intended regression, the violated invariant, and acceptance criteria. Delete
an issue when its fix, regression coverage, and documentation land. Do not
leave the only reproduction in an uncommitted example, and do not quarantine
a regression (in `tests/mdtests.rs` or `tests/examples.rs`) without a
corresponding issue here.

Policy lives in the docs, not here: `AGENTS.md` for when tooling failures
block feature work and what always warrants an issue, the
[proof-failure triage guide](../docs/concepts/proof-failure-triage.md) for
classifying a failure before filing (including the smart-versus-simple
tactic rule), [Testing Click](../docs/internals/testing.md) for
quarantine, profiling order, and the expansion workflow, and
[Verification Efficiency](../docs/internals/verification-efficiency.md) for
the complexity contract and scaling-regression policy. Proposals without a
failing deterministic curve are not open roadmap items; file a narrow issue
when evidence exposes one.

## Architecture issues: 1

- [Verify user-defined arena region ownership](arena-resource-ownership.md)

## Soundness issues: 8

Reachable from ordinary C plus a sidecar (false "verified" verdict today):

- [Reconcile heap lifetime and resource state at the loop back edge](loop-heap-and-resource-frame.md)
- [Make `intro` bind a variable fresh with respect to the available facts](have-binder-capture.md)
- [Make surface proposition substitution capture-avoiding](surface-substitution-capture.md)
- [Route induction proofs through the kernel proof object](legacy-pure-theorem-checker.md)

Reachable through the kernel API; the surface's exact checks currently mask
them, and since the removal of double execution (2026-09-02) no whole-body
re-execution stands behind those checks any more:

- [Enforce binder freshness and simultaneous substitution in the kernel](kernel-binder-hygiene.md)
- [Stop trusting caller-supplied contract structure in rule certification](contract-rule-trust-boundary.md)
- [Salt call-havoc snapshots so interning cannot attach a narrower write set](call-havoc-fingerprint-collision.md)
- [Close five latent kernel asymmetries](kernel-hardening-batch.md)

## Functionality gaps: 30

C language coverage:

- [Extend the integer model beyond int32 and uint8](integer-types.md)
- [Accept standard C type spellings and typedefs](c-type-spellings.md)
- [Widen the struct model](struct-model.md)
- [Accept multi-function files, prototypes, and includes](multi-function-files-and-headers.md)
- [Model file-scope objects, statics, and string literals](global-variables.md)
- [Model break, continue, do-while, switch, and goto](non-structured-control-flow.md)
- [Parse the everyday C syntax the C0 frontend rejects](c-syntax-conveniences.md)
- [Allow function calls in expression position](calls-in-expressions.md)
- [Specify external and libc functions without a body](external-function-contracts.md)
- [Evaluate pointer relational comparison and pointer subtraction](pointer-comparison-and-subtraction.md)
- [Support pointer-to-pointer types](pointer-to-pointer.md)
- [Broaden allocation forms and array declarations](allocation-shapes-and-arrays.md)
- [Support taking the address of a parameter](address-of-parameter.md)
- [Placeholder for floating point, function pointers, varargs, volatile, and concurrency](far-horizon-c-features.md)
- [Verify one unchanged existing-source fixture](audit-existing-c-source-fidelity.md)

Semantics and reasoning:

- [Rank count-up loops, nested loops, recursion in loops, and compound measures](termination-ranking-coverage.md)
- [Reason about byte-width element indices](byte-element-index-reasoning.md)
- [Model out-of-object pointer formation as undefined behavior](pointer-arithmetic-overflow.md)
- [Prove a loop invariant that relates a havoced pointer local to the index](pointer-local-loop-invariants.md)
- [Extend arithmetic reasoning past affine terms](nonlinear-and-interval-reasoning.md)
- [Give the memory DAG's loop-havoc edge a write set](loop-havoc-write-set.md)
- [Allow memory reads in `requires` propositions](memory-reads-in-requires.md)
- [Join branches that differ in heap deallocation](conditional-deallocation-joins.md)
- [Let verified C construct the first unit of a declared resource](abstract-resource-construction.md)
- [Extend the resource algebra: fractions, persistent tokens, mutual recursion, symbolic coefficients](resource-algebra-extensions.md)
- [Offer unbounded integers on the specification side](mathematical-integers-in-specs.md)
- [Instantiate universals with symbolic bounds and index facts under folds](quantifier-reasoning-coverage.md)

Proof language and tooling:

- [Lift proof-shape restrictions that force restructuring](proof-shape-restrictions.md)
- [Export a machine-checkable proof artifact](exportable-certificate.md)
- [Split the two expansion census unit tests](split-expansion-census-tests.md)
