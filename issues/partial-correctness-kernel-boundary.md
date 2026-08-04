# Separate partial-correctness summaries from concrete execution

## Problem

Click already verifies annotated loops by invariant preservation without a
termination argument. That is the right model for C safety, but the kernel
represents the resulting abstract exits using the same execution propositions
as concrete finite execution.

The mismatch is clearest at opaque calls:

- `CFunctionExecutes` represents a function producing a particular outcome;
- applying `CVerifiedFunctionRule` always constructs a fresh `Return` outcome;
- that abstract return is packaged as a `CFunctionExecutes` theorem; and
- loop summaries similarly package an invariant-derived exit as
  `CStatementExecutes` even though invariant preservation does not prove that
  the loop ever exits.

Assuming a hypothetical return satisfying a verified postcondition is sound
while checking all *terminating* caller executions. It is not a proof that the
callee actually returns. Keeping both meanings behind one proposition makes a
future recursion rule especially dangerous: the partial-correctness recursion
rule can validly prove any postcondition of `f() { return f(); }`, but it must
not thereby prove that `f` returns.

## Semantic contract

Surface C contracts should mean partial correctness by default:

- `requires P` restricts valid entry states;
- checked undefined behavior and contract violations cannot occur at any
  finite point of an execution beginning in such a state;
- `ensures Q` and returned resources apply to every execution that returns;
- resource authority constrains every finite memory access, and function-level
  effect clauses constrain every finite write in their declared footprint,
  including writes on a path that later diverges; and
- the contract makes no termination claim unless a separate termination
  certificate exists.

An infinite execution is not a `CFunctionOutcome::Diverges` value in the
ordinary finite big-step relation. It simply has no finite return outcome. The
kernel nevertheless needs a safety/contract judgment that can be certified
without constructing such an outcome.

## Desired kernel boundary

Keep concrete finite execution and modular verification distinct.

- A concrete `CStatementExecutes` or `CFunctionExecutes` theorem must continue
  to mean that the represented finite outcome actually follows from the
  operational semantics.
- A verified function contract should instead prove a universal conditional:
  any actual terminating execution satisfying the requirements has an allowed
  effect, returns the promised resources, and satisfies the postconditions.
- A loop rule should prove invariant initialization, preservation, finite-prefix
  safety, and facts about any actual exit. It should not prove that an exit
  exists.
- Applying a summary may introduce an abstract return branch while verifying a
  terminating caller path, but the resulting certificate must remain
  conditional on an actual return. It must never mint an unconditional
  concrete-execution theorem.
- Body safety, partial contract correctness, and termination evidence should be
  separate unforgeable kernel objects. Possessing the first two must not be a
  constructor for the third.

Exact Rust type and proposition names can follow the implementation, but terms
such as `Execution`, `Return`, and `Terminates` should be reserved for judgments
that really establish those facts. The kernel documentation should state the
inference boundary, not merely describe the symbolic implementation.

Treating `mutable` only as a comparison between entry and return memory would
make it vacuous for a divergent function and would permit temporary
out-of-footprint writes. Preserve its existing write-footprint meaning across
all finite prefixes. This remains useful even in Click's sequential model and
avoids painting future externally observable services into a corner.

## Proof-model check

The design should be justified against these two counterexamples:

```c
int32 spin() {
    while (1) {}
    return 0;
}
```

`spin` is safe and partially satisfies every return postcondition, but there is
no `CFunctionExecutes(..., Return(...))` theorem.

```c
int32 bad() {
    while (1) {
        return 1 / 0;
    }
}
```

`bad` is not safe merely because it lacks a valid return. Undefined behavior
is a finite bad outcome and must still be rejected.

## Tests

Add kernel-level tests, rather than relying only on Surface Click diagnostics:

- a verified invariant for `while (1)` cannot construct a concrete normal-exit
  theorem;
- a partial contract for `spin` cannot construct a concrete return theorem;
- the same contract can construct body-safety and partial-correctness evidence;
- a caller-summary transition remains conditional on the callee returning;
- no public combination of partial-contract objects constructs termination
  evidence; and
- ordinary bounded concrete execution still produces the existing execution
  theorems.

The negative tests should inspect proposition shapes or constructor
availability. A passing high-level proof alone would not catch the original
conflation.

## Documentation

Update at least:

- `docs/basic/what-click-is.md` and `docs/basic/contracts.md` to say “if the
  function returns”;
- `docs/intermediate/loops-and-invariants.md` to distinguish preservation from
  termination;
- `docs/click-language.md` to define the meaning of `ensures` and returned
  resources on divergent paths; and
- `docs/kernel.md` to document the concrete-execution, partial-contract, and
  termination boundaries.

Avoid saying merely that “every path satisfies `ensures`”: distinguish finite
return paths, finite bad paths, and infinite executions.

## Acceptance criteria

- Opaque function and loop summaries no longer claim concrete finite execution
  solely from invariant or contract certification.
- The verifier can continue to use summaries modularly on hypothetical return
  branches.
- Existing terminating examples retain their behavior.
- Kernel tests lock down the non-derivability of termination from partial
  correctness.
- User and kernel documentation describe one consistent semantic model.
