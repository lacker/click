# Resource unfold after a call rejects its pure-fact delta

Soundness: incomplete. A surface `unfold` of a held composite resource produces
facts that its kernel rewrite certificate rejects. This is disagreement between
the proof producer and checker, not evidence of false acceptance.

This reproduces on bounded-model recovery checkpoint `02bb7ccb8`; current
upstream rejects this archive contract spelling earlier, so no upstream failure
is claimed. The [reproduction](resource-unfold-after-call-rejects-checked-delta/repro.md)
keeps a descriptor, a separately owned backing cell, an allocation token and an
explicit descriptor/backing separation fact. `renew` consumes and produces the
composite; the caller then unfolds the returned composite. It fails with:

```
kernel rejected checked resource `unfold`
resource rewrite produced an unchecked pure-fact delta
```

```
click verify --trace-proof caller bugs/resource-unfold-after-call-rejects-checked-delta/repro.md
click verify --trace-proof renew bugs/resource-unfold-after-call-rejects-checked-delta/repro.md
click verify --trace-proof advance bugs/resource-unfold-after-call-rejects-checked-delta/repro.md
```

The latter two selected body proofs pass. Removing backing ownership and its
separation fact gives a passing two-call control. Do not infer that this is the
same failure as the original vector allocation fold: that original case gets
past the unfold and rejects full pointer-value equality during token matching.

Acceptance: retain the original C and separation promise, make resource
production and checked unfold agree, and check fresh, expanded, rewritten and
retained verification. Do not bypass the pure-fact delta check or reinterpret
address equality as full pointer-value equality.
