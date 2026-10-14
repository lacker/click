# Repeated zlib scalar tail cannot recover its held native byte-read authority

Soundness: incomplete. The selected initialized input and positive remaining
count make the original pre-increment byte read valid, but the proof's held
native views do not authorize it through the current resource-matching path.
No false acceptance is known. A repair must recover held authority rather than
promote a pure viewability fact into permission.

The unchanged zlib proof draft retains a caller view of the complete input and
loop views of its remaining bytes. In the nonempty scalar-tail branch, it
proves the remaining count positive, identifies the actual pre-increment
pointer, and constructs a checked one-byte viewability fact at that pointer.
The actual C read must still obtain authority from the held resources; the
viewability fact alone must never mint read authority.

After bounded selected-premise reduction removes the earlier 71-premise
presentation failure, the original read is refused at
`design/charon-trial/zlib/repeated-proof.click.draft:785`:

```text
missing resource fact `views ((char *)__click_call_result3)[0]`
C operation: adler = (adler + *__click_call_result3)
C statement at adler32.c:116:13: adler += *buf++;
```

This was reproduced twice with the draft, pinned C, headers, prepared input and
locks unchanged. A focused trace shows the checked native one-byte view,
the pre-increment pointer equations and byte observations before the read.
Adding an ordinary int32-count viewability fact for the same pointer also
checks but does not repair the resource-backed read. That is diagnostic
evidence, not a proposed authority workaround or a demonstrated root cause.
The original short-loop proof supports the corresponding post-increment
read for lengths 2–15.

## Reproduce

Build Click from the branch containing selected-premise reduction. Work on a
throwaway copy so the draft is not published as a verified sidecar:

```sh
mkdir -p work/repeated-checksum
cp -a design work/repeated-checksum/
cd work/repeated-checksum/design/charon-trial/zlib
cp repeated-proof.click.draft repeated.click
cp short-memory.click.import.json repeated.click.import.json
cp short-memory.click.import.lock.json repeated.click.import.lock.json
```

Run the built `click verify --trace-proof adler32_z repeated.click` against that
copy. The relative imports and prepared input remain intact. Preparation need
not run again. The selected source is zlib 1.3.1 revision
`51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf`; its source hashes and build boundary
are documented in the trial README.

## Intended regression and acceptance

- Reduce the two-loop, full-width moving-cursor pattern to a bounded gate case
  and determine which held range should authorize the original byte read.
  Preserve native counts, actual post-increment semantics and lifetime checks.
- Repair resource matching or the proof's legitimate frame so the read obtains
  that held authority. A pure `viewable` fact must not grant a resource; missing
  views, an out-of-range read and a stale lifetime must remain rejected.
- Recheck the unchanged repeated-block draft, its component invariants and
  final checksum before promoting it. Verify, profile and expanded
  certificates must agree. Do not raise budgets, narrow the input domain or
  change the original C to bypass the failure.
