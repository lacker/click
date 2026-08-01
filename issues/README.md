# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases are skipped by the explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`.

| Issue | Status | Covers |
|---|---|---|
| [Certificate spelling gap](certificate-spelling-gap.md) | Partially fixed; owned-string certificate failures and two earlier regressions fixed | Field-derived effect-chain claims |
| [Field-derived slow fold](field-derived-slow-fold.md) | Still independently reproducible | A slow simple `fold` in one quarantined mdtest |
| [Owned-string slow proof](owned-string-slow-proof.md) | Correctness fixed; full gate exceeds 10 minutes | The quarantined owned-string example |
| [Owned-vector implication gap](owned-vector-implies-gap.md) | Stale frontier; profile after certificate spelling | The quarantined owned-vector example |
| [Local pointer spelling workaround](local-pointer-spelling-workaround.md) | Passing workaround | One explicit `have` that certificate generation should eventually remove |
| [Language cleanup shortlist](language-cleanup-shortlist.md) | Parked | Small owner-approved surface cleanup for a later language arc |

Keep one file per independent open problem. Put durable implementation design
in `docs/`, and delete an issue when its fix and regression coverage land.
