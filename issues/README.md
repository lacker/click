# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases are skipped by the explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`.

| Issue | Status | Covers |
|---|---|---|
| [Certificate spelling gap](certificate-spelling-gap.md) | Partially fixed; one mdtest de-quarantined and one correctness frontier cleared | Field-derived effect-chain claims and owned-string's next failure frontier |
| [Vector close-invariants cost](vector-close-invariants-slow.md) | Correctness passes; deterministic replay is over budget | One quarantined mdtest |
| [Owned-string loadable bridging cost](owned-string-loadable-bridging-slow.md) | Independent performance bug | The multi-minute owned-string run |
| [Field-derived slow fold](field-derived-slow-fold.md) | Still independently reproducible | A slow simple `fold` in one quarantined mdtest |
| [Owned-vector implication gap](owned-vector-implies-gap.md) | Stale frontier; profile after certificate spelling | The quarantined owned-vector example |
| [Local pointer spelling workaround](local-pointer-spelling-workaround.md) | Passing workaround | One explicit `have` that certificate generation should eventually remove |
| [Language cleanup shortlist](language-cleanup-shortlist.md) | Parked | Small owner-approved surface cleanup for a later language arc |

Keep one file per independent open problem. Put durable implementation design
in `docs/`, and delete an issue when its fix and regression coverage land.
