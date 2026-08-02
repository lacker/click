# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases belong in explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`, with a corresponding issue here.

## Surface-language cleanup

The remaining stylistic cleanup is split into independently reviewable
changes:

1. [Remove redundancy from exact-premise tactics](exact-premise-syntax-cleanup.md).
2. [Canonicalize proof spelling and generated ranges](canonical-proof-spelling-and-printing.md).
3. [Distinguish authoring syntax from expanded certificates](authoring-vs-certificate-documentation.md).
4. [Unify Click-native binder spelling](click-native-binder-consistency.md)
   (optional and lower priority).

The first issue is the highest-value language change. The second is a small
source-and-printer cleanup. The documentation issue should follow the syntax
work so it describes the resulting surface accurately. Binder unification is
a mechanical consistency improvement, but it should not block the other three.
