# Loadable DAG bridging is hot (owned-string 2.6 s -> 5m26s to fail)

Status: open (small; profile first)
Claimed:

The extended DAG bridging that closed the loadable gap (2026-07-31:
BlockDeclared/CellsForgotten edges, scoped via
`with_extended_dag_bridging` to `Assumptions::proves_memory_loadable`)
runs inside every loadable check, and owned-string now takes 5m26s to
reach its next frontier (was 2.6 s to the old one). Recorded cause
hypotheses from the closing agent: the bridging walks are hot, and the
memo is generation-invalidated by load-caching stores. Profile with
`click-profile` / call-site counters BEFORE optimizing or extending;
the corpus gates are unaffected (mdtests 7 s, examples 6.4 s) so this
only bites snapshot-heavy quarantined members today — but it becomes a
gate cost the moment owned-string de-quarantines.

Prior record: notes/tasks/owned-string-loadable.md history in git
(deleted at close), notes/memory-dag.md (edge-kind semantics).
