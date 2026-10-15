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

## Native input coordinate follow-up

The [refold-and-return reduction](resource-unfold-after-call-rejects-checked-delta/refold-and-return.md)
previously lost its admitted native prefix: normalization skipped the stored
witness at an intermediate snapshot. The repair indexes exact and unconditional
read identities, selects one live witness, and transports the queried complete
pointer read into that witness's original coordinates through retained full-cell
frame evidence. It preserves displacement and access qualifiers; numeric address
equality alone supplies no native input. Stored witness addresses do not change.

The reduction verifies all three proofs and passes fresh, expanded, rewritten
and retained checks. All 220 selected native-input, span, pointer-domain, memory
provenance, substitution and resource-delta controls pass. The new deterministic
regression covers unrelated row counts 0/16/64/256, three storage-address forms,
offsets, type/qualifier checks, partial overwrites, ambiguous inputs and retirement.

At checkpoint `576012956`, the [refold-and-free reduction](resource-unfold-after-call-rejects-checked-delta/refold-and-free.md)
still rejected `free`: allocation discovery required an exact raw pointer spelling.
The follow-up below repairs that separate lookup failure.
The original vector and the ten-failure archive audit remain unresolved; no
new green archive verdict or upstream native-model activation is claimed.

## Selected owner retirement repaired

The allocation token's source read and the `free` argument pass the existing
complete-pointer-value comparison under the current separation facts. However,
the resource index omitted the token: publication indexed an unconditional
endpoint, while the query normalized past it under scoped facts. Candidate
discovery now includes intermediate read names from the selected complete-cell
walk. It scans no unrelated resources and grants no authority; the selected
owner still must pass the full-value comparison. Execution retires that owner's
original coordinates, consumes its allocation token and complete backing
ownership, and checks active loans and lifetime retirement as before.

Native-input lookup shares that selected-history discovery. An ambiguous bucket
is refused by its size without copying its members. The conditional-frame
regression also checks that retirement removes the selected native witness.

The refold-and-free reduction verifies all three proofs and passes fresh,
expanded, rewritten and retained checks with a rebuilt library; the return
reduction still passes all four modes. All 312 selected resource, heap, native
input, span, provenance, substitution and pointer-result controls pass, as do
90 pointer-store, independent-entry and proof-execution controls. The new
0/16/64/256 unrelated-token regression rejects interior pointers, numeric-only
aliases, partial upper-half overwrites, double frees and active loans.

The original two-call reduction now reaches its later allocation fold after
`advance`, which still loses the full field value across that modular call. The
original vector still rejects its allocation fold. Neither this repair nor the
passing reductions establish archive activation or a new normal-audit result.
