# C pointer-field postconditions lose checked frame evidence

Priority: P1.

Soundness: incomplete. The verifier rejects unchanged supported C proofs. This
reproduction does not demonstrate acceptance of a false claim.

In the initial PR 646 bounded-object-model reproduction, the original
`examples/owned-vector/vector.click` rejects `vector_push` at its final
`assumption` steps: `owner->data == old(owner->data)` and
`owner->data[old(owner->len)] == value` remain unproved. The C body stores through
the backing pointer and then increments the descriptor's length. Its
`vector_storage` contract already separates the entire descriptor from the
backing range, and its precondition places the index inside that range.

A focused reproduction uses the unchanged `vector_push.c`, the original
`vector_storage` definition, and the original `vector_push` contract/proof;
other functions and resources are unnecessary. Inserting the diagnostic-only
claim `have owner->data == old(owner->data) by { assumption(); }` immediately
after the existing `fold(vector_storage(owner))` exposes the failure with
`--trace-proof vector_push`. The trace stops the eight-byte pointer-field read
at the four-byte backing-element store. Adding that same claim with `simp`
closes the pointer equality but still leaves the stored-element postcondition
unproved. Neither experiment changes the C or weakens its claims.

Private instrumentation found selected separation evidence whose write and
full read memberships both check, with no alias veto. That does not yet
identify why the failing comparison cannot use the evidence; do not replace
this investigation with an address-only origin rule. The original
`examples/owned-string/owned_string.click` also fails its stored-element
postcondition after the same kind of backing write.

Acceptance criteria:

- Verify the original vector and string projects with their C and claims
  unchanged, including the original frame and stored-value postconditions.
- Reduce the missing comparison into a regression that verifies, expands,
  verifies its rewritten proof, and rechecks a retained certificate.
- Reject controls removing the separation or allowing the write to overlap
  the descriptor, and reject a wrong stored-value claim.
- Preserve full pointer origins: numeric address equations must not establish
  native place validity or replace the pointer stored in a field.
- Keep existing proof and timing limits; profile only after the proof succeeds.

## Current progress after the scoped read-producer repair

PR #1023 fixes the intervening two-write execution gap. Explicit checked
equalities now prove the original `owned_string_set` and `vector_push`
contracts: the setter proves its stored element with `simp`, and vector push
proves its backing pointer unchanged and its stored element before folding.
The final `assumption` steps remain exact-fact lookup; no kernel rule changes.

The complete recovery projects are still rejected. String push reaches the
terminator equality `owner->data[owner->len] == 0`; its trace distinguishes the
pointer read used by the zero store from the later projected pointer read. A
direct `simp` attempt also rejects that equality despite the held
descriptor/backing separation. Vector proceeds past `vector_push` and fails a
later `allocated_vector_push` allocation-resource fold. Keep this report open
until its full-project acceptance criteria are met.

## Upstream proof recovery versus archive activation

PR #1027 landed the explicit setter/vector equalities. On upstream's kernel,
`owned_string_push` additionally verifies after explicitly proving
`owner->data == old(owner->data)` and using `simp` for the unfolded terminator.
With that proof adjustment, the full owned-string project (15 proofs) and the
full owned-vector project (13 proofs) verify; their C and contracts are intact.
The setter/vector reduced four-mode checks in #1027 do not by themselves
establish this full-project result.

The recovery archive at `d6caff076` still rejects that explicit backing-pointer
equality after the terminator store. Its trace stops an eight-byte pointer-field
read at the four-byte zero store. The write address contains a pointer read
projected from the first backing store's exit; the final field read projects
from the zero store's exit. Descriptor/backing separation is held. The same
explicit equality succeeds on upstream, so this is an archive compatibility
obligation, not a reason to weaken the example or broaden `assumption`.
The archive also still rejects the later allocation fold described above.
Keep this report open for recovery activation; do not equate upstream example
success with closure of those two archive failures.

## More precise split-field reduction

Explicitly proving `0 <= old(owner->len) + 1` lets the archive check the final
backing-pointer equality across the terminator store. The resource keeps its
original separate descriptor fields. Explicit stored-value and unfolded
terminator facts then check, but the subsequent simple resource fold exhausts
its deterministic work budget. The
[historical reduced fold defect](https://github.com/lacker/click/blob/ee9b29f87822302f753f53eeb1c505bcc06f21ea/bugs/split-descriptor-fold-exhausts-simple-budget.md) preserves
this next blocker and the profile. No claim that the full archive project
passes, and no new full-audit count, follows from this reduction.

## Archive string project recovered

At `e5305eeba` plus explicit `unfold(terminated_at)` in clear, the full original
owned-string project verifies all 15 proofs. The full project with the push
expansion, and focused original pop and clear reductions, pass fresh, expanded,
rewritten and retained checking with a freshly rebuilt library. The normal
52-project archive audit now passes 42 and fails 10 (176.3s harness, exit 100);
string is no longer among its failures. The separate vector allocation fold
remains, alongside arena, binary-tree, input-cursor, multifile-registry,
rbtree-augmented, refcount, ring-buffer, rust-byte-sum and rust-chunks-exact.
This is a partial audit, not a green archive verdict.

The split-field fold's final indexed-order variant passes all four modes.
Its completed profile still finds an expensive first returned-resource
assumption; track that independently in the
[return-resource performance report](split-descriptor-return-resource-check-repeats-work.md).

## Allocation-fold argument isolated

On `02bb7ccb8`, private argument-local probes confirm that the original
`allocated_vector_push` fold rejects its allocation token's pointer argument
before comparing the byte count. Its two loaded pointer carriers have different
snapshot identities. Numeric address equality is checked successfully, but full
carrier equality is not. The existing inferred member effects certify final
full-width writes selected through authenticated record roots; the push body
leaves the pointer field unchanged. This identifies the missing evidence, not a
justification to widen numeric equality or activate native semantics from C
layout metadata. The smaller
[checked-unfold mismatch](resource-unfold-after-call-rejects-checked-delta.md)
is preserved separately and is not yet established as the same cause.

The latest completed normal archive audit at `80eb92029` remains 42/52, with the
same ten failures (136.3s harness, exit 100). The string project still passes.
The bounded fold repair is delivered upstream in PR #1051; the separate
read-frame delta reduction passes all four modes. These do not close the vector
allocation fold or the native-place check exposed by the two-call reduction.

## C field-source prerequisite

The recovery field reader now separates ordinary C member observation from
native record authentication. Its C-allocated-access path evaluates the existing
checked `MemberAddress`, then requires initialized complete pointer bytes and
ordinary read authority. Both the state and callee interface must permit C
allocated access. It does not create a native record witness, alter the stored
pointer's origin, or make an address-only equation a complete value equation.
Native-designated fields retain their existing authenticated selection checks.

The new control preserves a full stored pointer while the descriptor remains
without a native designation. It rejects missing read authority, partial
initialization, a mismatched field/type, a wrong qualifier, and native-only
state or interface policy. This is a prerequisite only: C field candidates and
universal body-certified preservation still need to be connected to modular
application. No new original-vector result or archive audit is claimed.

All 33 selected field-source, pointer-result and independent-entry controls pass
(0.38s harness); formatting and whitespace checks pass. The initial test setup
had two compile errors, corrected before this accepted run.

## Direct-input preservation certified in the kernel

The archive now certifies unchanged ordinary C pointer fields from complete
independent body execution and transfers their full values at modular calls.
It requires complete initialized input bytes and read authority, and rejects
every overlapping write, including a full equal-address replacement. Owned
and viewed input controls pass without creating a native record witness.
Cached field identity, selected-body discovery and once-per-claim-batch inference
have deterministic multi-size controls. All 96 focused controls and 337 broader
kernel controls pass.

This does not close source-level activation. The folded-resource frontend
materializes three cached read names absent from independently reconstructed
entry memory; exact entry matching therefore rejects the summary. Resolve that
checked observation protocol without importing arbitrary caller values or
weakening independent certification. No new original-vector or audit result is
claimed.
