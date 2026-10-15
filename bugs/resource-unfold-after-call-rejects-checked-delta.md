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

## Selected read-frame repair

The rejected fact is `CMemoryLoadable`, with the same memory snapshot, byte
count and retirement metadata as an instantiated body premise, but another
registered name for its backing address. The premise is uniquely selected; the
existing exact-only equality bridge cannot consume the recorded complete-cell
frame connecting the two pointer reads.

The candidate keeps source selection unchanged and checks only that selected
pair's full-width pointer-read frame. Its evidence is retained in the existing
rewrite capture and rechecked with the call events. It proves address equality
for loadability, not a new referent designation. Overwritten, partial and narrow
reads reject; unrelated fact counts 0, 16, 64 and 256 keep selected work bounded.
The existing ambiguity and lifetime controls remain unchanged.

All 337 selected kernel execution, memory, native-record and pointer-effect
controls pass. The focused [unfold-and-free reduction](resource-unfold-after-call-rejects-checked-delta/unfold-and-free.md)
verifies all three proofs and passes fresh, expanded, rewritten and retained
checking with a rebuilt library. The original two-call case gets past `unfold`
and next rejects its `fold(storage(owner))` native-place carrier check. Keep
that separate from this repaired producer/checker mismatch and from the
original vector token comparison. Upstream extraction remains pending.
