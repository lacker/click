# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases are skipped by the explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`.

| Issue | Status | Covers |
|---|---|---|
| [Local pointer spelling workaround](local-pointer-spelling-workaround.md) | Passing workaround | One explicit `have` that certificate generation should eventually remove |
| [Language cleanup shortlist](language-cleanup-shortlist.md) | Parked | Small owner-approved surface cleanup for a later language arc |

Keep one file per independent open problem. Put durable implementation design
in `docs/`, and delete an issue when its fix and regression coverage land.
