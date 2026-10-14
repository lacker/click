# Native composite output checking requires an already decided body guard

Soundness: incomplete. The archived object-model implementation rejects an
ordinary C caller that receives and consumes a verified conditional resource.
The producer has checked both allocation outcomes, so the caller may use the
conditional head without deciding whether allocation succeeded. No false
acceptance is demonstrated by this regression.

Priority: P2. Branch compatibility defect; blocks activating the affected model.

## Reproduction and revisions

The following complete C/Click witness passes fresh, expanded, rewritten and
retained checking on the `b8f7a8ea1`-based captured-pointer extraction submitted
in PR #926. The frozen archive `e3d84a785` rejects `probe.contract` while applying
`create`: `native composite body guard is not established`.

# Conditional allocated-record output is reusable without deciding its guard
```c filename=probe.c
struct box { int32 value; };
struct box* create(int32 value) {
    struct box* p = malloc(sizeof(struct box));
    if (p != 0) { p->value = value; }
    return p;
}
void dispose(struct box* p) { if (p != 0) { free(p); } }
int32 probe(int32 value) {
    struct box* p = create(value);
    dispose(p);
    return 0;
}
```
```click
verifying "probe.c";
resource box(p: struct box*) {
    if p != 0 {
        owns allocation(p, sizeof(struct box));
        owns *p;
    }
}
struct box* create(int32 value) {
    produces box(result);
} by { execute(); fold(box(result)); simp(); }
void dispose(struct box* p) {
    consumes box(p);
} by {
    if p != 0 { unfold(box(p)); execute(); simp(); }
    else { unfold(box(p)); execute(); simp(); }
}
int32 probe(int32 value) {
    ensures result == 0;
} by { execute(); simp(); }
```
```expect
pass
```

## Invariant and reduction evidence

The original `allocated-linked-list` and `heap-object` projects exhibit the
same refusal. The list trace already contains the initial null result, but
the next producer's post-state has a new result that may be null or nonnull.
A temporary probe records the resource guard on that new result and the
producer's disjunctive result guarantees; the caller cannot decide the guard.

`check_native_composite_formation` in
`src/kernel/functions/native_record_inputs.rs` calls
`evaluate_composite_resource_body_condition` before checking the selected
body. Its `None` arm refuses the verified conditional output. The declaration
has automatic ordinary C record-place metadata; that metadata must respect the
C allocation/access policy and must not activate C++ object requirements.
The reduction establishes this failure path, not its introducing commit.

Changing the model-parameter setter to `bind_logical_typed` does not repair the
original list failure. That experiment is discarded. Do not rename the C local,
split the caller into explicit null branches, or weaken the resource to evade
the output check.

## Acceptance

- Preserve the original producer and caller, including unknown allocation
  success and conditional ownership of the initialized record.
- Check actual guarded native promises without requiring a caller to decide
  every guard before transferring an already checked resource head.
- Preserve explicit `valid_place` checks and C++ declaration, origin and
  lifetime checks; ordinary C layout metadata grants no C++ witness.
- Recheck both original projects, this reduction, and forged native-object,
  expired-pointer and insufficient-output rejection controls.
- Verify ordinary proofs, expansion, rewritten proofs and retained checking.
- Keep checks bounded by the selected head and its body; do not scan unrelated
  resources or invoke unbounded proof search to decide the guard.

## Isolated archive repair checkpoint

A local repair against `e3d84a785` classifies ordinary C legacy record metadata
before asking for the composite guard. It uses the existing access policy,
retained designation and declaration identity, and does not bypass native span
or record-prefix requirements. The original allocated-linked-list and
heap-object projects both pass, as does the reduced producer/caller witness.

Three focused kernel controls pass: conditional legacy metadata, absence of
native validity for ordinary C metadata, and checked native-prefix field-read
authority. Both native C++ member-domain rejection Markdown controls pass.
The ordinary C scalar-subobject P1 is separate and remains open.

This patch depends on archived native-entry machinery absent from master. It
is preserved as a candidate for the corresponding complete activation slice,
not submitted as a standalone patch or a green verdict for the archive.
