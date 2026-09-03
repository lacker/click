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

## Architecture issues: 2

- [Remove search, fuel, and fallbacks from the kernel](simplify-kernel.md)
- [Verify user-defined arena region ownership](arena-resource-ownership.md)

## Functionality gaps: 31

C language coverage:

- [Extend the integer model beyond int32 and uint8](integer-types.md)
- [Widen the struct model](struct-model.md)
- [Accept multi-function files, prototypes, and includes](multi-function-files-and-headers.md)
- [Model file-scope objects, statics, and string literals](global-variables.md)
- [Model forward and backward goto edges](goto.md)
- [Allow function calls in expression position](calls-in-expressions.md)
- [Specify external and libc functions without a body](external-function-contracts.md)
- [Broaden allocation forms and array declarations](allocation-shapes-and-arrays.md)
- [Model floating-point values](floating-point.md)
- [Model variadic functions](variadic-functions.md)
- [Model volatile objects](volatile-objects.md)
- [Model concurrency and atomics](concurrency-and-atomics.md)
- [Lift the block-scoped declaration restriction](block-scoped-declarations.md)

Semantics and reasoning:

- [Rank count-up loops, nested loops, recursion in loops, and compound measures](termination-ranking-coverage.md)
- [Extend the resource algebra: fractions, persistent tokens, mutual recursion, symbolic coefficients](resource-algebra-extensions.md)
- [Offer unbounded integers on the specification side](mathematical-integers-in-specs.md)

Proof language and tooling:

- [Export a machine-checkable proof artifact](exportable-certificate.md)
