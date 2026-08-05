# Add dependency-aware incremental verification

## Problem

The enlarged owned-vector sidecar contains eleven functions and forty-eight
claims and takes roughly fifteen seconds to verify even though profiling finds
no unhealthy operation. Healthy linear work is unavoidable, but repeatedly
checking unaffected claims will make the ordinary edit/verify loop approach
the per-sidecar deadline as projects grow.

Users should not have to split natural C projects or route every edit through a
manually selected source coordinate merely to keep verification responsive.
The existing targeted `PATH:LINE:COLUMN` entry point proves that Click can
verify a proof unit and its called dependencies, but there is no native
dependency-aware project workflow or reusable verified-result cache.

## Invariant

Incremental verification is an optimization of full verification, not a new
source of axioms. A cached or skipped result is usable only when all semantic
inputs to that theorem are identical and every changed dependency is
reverified. Ambiguity must cause conservative rechecking.

## Design

- Define the semantic fingerprint of a verified proof unit: parsed C body,
  Click contract and proof, imported type/layout environment, called function
  contracts, resource and theorem definitions, verifier build/schema version,
  and proof-affecting configuration.
- Record the dependency graph already used by targeted verification and expose
  why a claim was selected or invalidated.
- Begin with reuse inside one native CLI project run. A later persistent cache
  must be content-addressed and atomically written; timestamps alone are not a
  valid key.
- Provide a native changed-project mode that selects changed claims and their
  reverse dependents. It should also support a dry-run explanation without
  proving anything.
- A change to parser, kernel, proof engine, builtins, target ABI, or cache schema
  invalidates every affected cached theorem. When that set cannot be proved
  narrow, invalidate all of it.
- Keep full `click verify` available as the reference gate and periodically
  compare incremental and clean outcomes in tests.
- Use the shared verification engine directly. Do not construct the feature by
  recursively invoking Click or scraping child-process output.

## Regression

Use a three-function project in which `top` calls `middle`, `middle` calls
`leaf`, and an unrelated function is independent. After an initial complete
run:

- changing only the unrelated proof selects only that proof unit;
- changing `leaf` selects `leaf`, `middle`, and `top`;
- changing a resource or called contract selects every consumer;
- changing only comments or formatting does not invalidate semantic results;
- changing proof-affecting configuration or the cache schema forces the
  appropriate conservative rebuild.

Run the selected set through the same direct verifier entry point and compare
its final success or failure with a clean full verification.

## Acceptance criteria

- Incremental and clean verification agree on every regression outcome.
- The tool prints a bounded explanation of selected, reused, and invalidated
  claims.
- A one-function edit in a larger independent project avoids rechecking
  unrelated claims and materially shortens the second run.
- Dependency, environment, engine, and schema changes cannot reuse stale
  theorems.
- Cache corruption or interruption causes a safe miss, not acceptance or a
  stuck worker.
- No project restructuring, wrapper script, or hidden recursive CLI mode is
  required.
