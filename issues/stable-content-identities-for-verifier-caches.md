# Verifier caches use bounded linear scans with deep structural keys

Recent success-only caches remove important duplicate work, but several store
complete states, functions, assumptions, environments, outcomes, or resource
contexts in small vectors. Lookup scans the cache and compares these values
structurally. In a larger project, proving cache equality can approach the cost
of the computation being avoided, and storing an entry duplicates large
objects.

The caches are sound because they retain only complete successes and exclude
limited executions. This issue is about their identity and asymptotic cost, not
their logical policy.

## Required design

Give immutable semantic values stable session-local identities backed by
canonical interning or cached content fingerprints with collision-safe equality.
Build typed cache keys from those identities and scalar mode flags. Use indexed
bounded maps with explicit ownership/lifetime rather than thread-local vectors
whose entries can outlive the verification unit that made them relevant.

Failures and deadline-limited results must remain uncached. Cross-session or
persistent cache reuse is out of scope unless a separate trust design is
approved.

## Regression design

Populate each hot cache with increasing numbers of large, unequal entries,
then query a hit and a miss whose semantic input size is fixed. Separately
prove that equal persistent views share a key and that a one-field change does
not. Count key-construction and lookup work.

## Acceptance criteria

- Cache lookup is logarithmic or constant in entry count after key creation.
- Key creation does not traverse a complete environment or proof history.
- Entries structurally share their large immutable inputs.
- Cache scope is tied to a verification session.
- Existing success-only and deadline-safety regressions remain green.
