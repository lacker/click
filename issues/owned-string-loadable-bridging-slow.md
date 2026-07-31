# Loadable DAG bridging is ~100x too slow on owned-string

The scoped DAG bridging that closed owned-string's loadable gap
(2026-07-31: `BlockDeclared`/`CellsForgotten` edges, scoped via
`with_extended_dag_bridging` to `Assumptions::proves_memory_loadable`)
made the example take 5m26s to reach its next frontier (was 2.6 s to
the old one). Deterministic and correct, but a rule-5 engine cost; it
must be fixed before owned-string can de-quarantine.

Recorded mechanism: the walk runs inside every loadable check, and the
memo key includes the global derivation-generation counter, which every
store bumps — so the cache is wiped constantly.

Likely cheap fix (unverified): DAG edges are append-only with
first-wins recording, so POSITIVE connectivity answers are monotone —
they can be cached without generation invalidation; only negative
answers can go stale. Split the cache accordingly. Profile first
(`click-profile`, call-site counters); corpus gates are currently
unaffected (only quarantined members hit this).
