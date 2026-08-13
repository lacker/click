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

Scaling axis: cache entry count with one fixed-size hit and miss, measured
separately from semantic input size. Each migrated cache must add this
four-size curve plus the equal-view/one-field-change identity regression before
the issue can close.

## Acceptance criteria

- Cache lookup is logarithmic or constant in entry count after key creation.
- Key creation does not traverse a complete environment or proof history.
- Entries structurally share their large immutable inputs.
- Cache scope is tied to a verification session.
- Existing success-only and deadline-safety regressions remain green.

## 2026-08-13 progress

The closed context-free `forall` success cache now uses an ordered exact set.
A hit no longer clones the complete cache and then scans it linearly; only a
miss materializes the retained closed facts needed to prove a new entry. The
success-only and active-limit exclusion policy is unchanged.

The larger issue remains open: independent execution and resource
representation caches still retain bounded vectors with deep structural keys,
and cache lifetime is not yet tied to one verification session.

Checked execution reuse now deliberately refuses to probe definitional entry
resource equality for recursive composite definitions. A binary-tree
measurement showed that using the general recursive relation as a cache-key
equivalence test costs about 9.5 seconds by itself. Stable shallow identities
for recursive resource projections are therefore a prerequisite to extending
that reuse path; fresh body execution remains the bounded fallback.

The memory arena now has a session-local shallow index keyed by the identities
of `CMemory`'s immutable block, cell, and heap components. Re-interning an
already-retained snapshot therefore avoids hashing and comparing the complete
memory. Independently constructed equal snapshots retain the structural
fallback; their temporary component addresses are deliberately not cached,
because the arena does not retain those alternate components and allocator
reuse would make such a key unsound. This removes one deep-key cost from
memory-DAG and memo lookups, but the broader cache-key issue remains open for
states, assumptions, environments, and resource projections.

The snapshot-bridging `c_memory_load_is_unchanged` boundary now memoizes
complete answers under shallow memory identities, pointer, and an enclosing
assumptions identity. Proven successes remain valid; negative answers are
scoped to the memory-DAG derivation generation and are excluded after deadline
or search truncation. Callers without an explicit assumptions scope keep the
unmemoized behavior rather than paying a deep fact-set hash to construct a
cache key.

Top-level memory-resolution distinctness now shares the same typed,
assumptions-identity memo used by pointer and term equality. Pointer pairs are
canonicalized because distinctness is symmetric; positive results remain
valid, while negative results retain the derivation-generation and truncation
discipline. A deterministic regression requires a repeated distinctness query
to consume no additional verifier work. This removes thousands of repeated
explicit-range subqueries in the owned integration profiles, but callers still
need an enclosing shallow assumptions scope to use the memo.

Owned-vector exposes the next identity boundary in 28 unique range-coverage
queries totaling about 0.4s. The range bases and endpoints contain nested
memory loads from successive call-havoc snapshots. `SharedCMemory` equality
and hashing are shallow within one arena, but ordered proposition and term keys
still structurally compare the surrounding trees. The eventual term identity
must preserve deterministic structural presentation order separately from hot
lookup identity, just as the proof-fact stores do; another memo with deep term
keys is explicitly not the fix.
