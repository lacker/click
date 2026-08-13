# Smart proof search and the expansion gate duplicate checked replay

Every successful smart tactic constructs a surface-expressible simple
certificate and replays it before proof execution can continue. A grouped
claim containing any smart tactic later stitches those certificates and
replays the complete contract script again through the whole-claim expansion
gate. The second replay is sound and currently protects against stitching and
sequencing bugs, but it repeats deterministic kernel work already required by
the smart-tactic boundary.

After expanding owned-vector's sites above 300ms, a representative profile
still spends about 2.85 seconds across 11 `whole-contract certificate replay`
calls. Fully simple grouped scripts avoid this second pass because the source
script is definitionally its own certificate. Mixed scripts do not, even
though each generated fragment was replayed in its actual proof context.

## Required design

Do not remove or weaken the expansion hard gate. Instead, make successful
smart execution produce typed checked-replay artifacts that seal:

- the exact generated surface certificate fragment;
- the replay entry and exit proof-state identities;
- the source tactic and proof-unit identity;
- the checked theorem/claim delta; and
- the kernel semantics and environment identities under which replay ran.

The claim-level stitcher should compose adjacent artifacts only when their
sealed state identities link exactly. Source-simple regions need equivalent
checked segments, obtained from the ordinary replay that already executes
them. The final gate then validates the linked chain, complete claim coverage,
and the emitted stitched certificate without re-executing every tactic. Any
missing fragment, identity mismatch, blocked builder, or incomplete claim
coverage must fall back to full replay or fail; it must never be accepted from
planner state alone.

Tie this authority to one verification session. Stable identities required by
the artifact should use the design in
`stable-content-identities-for-verifier-caches.md`, not deep structural cache
keys. The type-level cleanup in `retire-simple-proof-builder-blocker.md` is a
natural prerequisite or companion because it makes an unrecorded fragment
unrepresentable.

## Regression design

Generate one grouped claim containing `K` alternating source-simple and smart
tactics. Count deterministic tactic replay executions and whole-script replay
work before and after stitching. The accepted certificate must still round
trip through `click expand`, verify cold, and reach an expansion fixed point.

Add negative tests that mutate one fragment, swap adjacent fragments, change
one replay entry fact, omit one grouped claim, and present an artifact from a
different verification session. Each must be rejected or force ordinary full
replay. Deadline-limited and failed smart attempts must never create an
artifact.

Scaling axis: number of checked certificate fragments in one grouped claim,
with fixed per-fragment work. Gate validation should be linear in certificate
output and must not perform a second kernel execution of every fragment.

## Acceptance criteria

- Smart tactics remain accepted only after a replayable surface certificate
  has been checked by the kernel.
- The final expansion gate still checks certificate completeness, sequencing,
  claim coverage, and emitted surface syntax.
- A checked fragment's kernel work is not repeated solely because the claim
  contains another smart fragment.
- Gate validation costs `O(K polylog N)` shallow work plus unavoidable emitted
  certificate output, with no second proof replay.
- The expansion audit, blocker regressions, full example suite, and all
  deadline/truncation safety tests stay green.
