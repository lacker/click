# A loop resource selector loses a framed descriptor's read authority

Soundness: incomplete. The archived object-model implementation rejects a
supported ordinary C loop proof when its resource argument reads a borrowed
pointer field. The field is outside the buffer writes. This witness demonstrates
rejection, not acceptance of a false claim.

Priority: P2. Branch regression blocking the affected activation.

## Reproduction

The following complete witness passes fresh verification, expansion, verification
of the expanded source and retained-session rechecking on the `7920aaf0e`-based
entry-fold repair delivered in PR #937. The recovery checkpoint `86abef177`
rejects `probe.loop(0).preserve` before checking its body:
`resource cells argument 1 could not be evaluated: required access authority is
unavailable; expression h->data`.

# A loop resource can select its backing through a framed descriptor field
```c filename=probe.c
struct holder { int32* data; };
void probe(struct holder* h, int32 n) {
    int32 i = 0;
    while (i < n) { h->data[i] = 1; i++; }
}
```
```click
verifying "probe.c";
resource cells(data: int32*, n: int32) { owns data[0..n]; }
void probe(struct holder* h, int32 n) {
    requires 0 <= n;
    requires n <= 536870911;
    views h->data;
    owns cells(h->data, n);
} by {
    step(); step();
    loop {
        owns cells(h->data, n);
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        initialize by simp;
        preserve by {
            unfold(cells(h->data, n));
            step(); step();
            fold(cells(h->data, n));
            close_invariants();
        }
    }
    execute(); simp();
}
```
```expect
pass
```

## Invariant and acceptance

The borrowed pointer field is actual descriptor-read authority. The loop's
owned buffer resource must not erase that authority while evaluating the loop
header or rebuilding the abstract head. Resource arguments remain checked reads;
do not bypass read authority or manufacture initialized pointers to make the
header evaluable. Numeric address equality remains separate from pointer origin.

The unchanged arena project fails with the same error while evaluating
`arena_window(arena->data, ...)`. This reduction identifies the small selector
boundary; a shared repair must still be demonstrated on the original project.

- Restore the reduction in all four proof modes and recheck original arena.
- Reject controls with missing descriptor-read authority, uninitialized pointer
  contents or a loop that may overwrite the descriptor without preserving the
  selector.
- Preserve existing loop exit argument rebinding and actual-call domain checks.
- Record the introducing change and keep current work and proof limits.

## Attributed cause and partial repair

The `MemberAddress` arm added by archived commit `3e6d4cc0e7` treats every
variable in the object expression as address-taken. For `h->data`, this marks
`h` as escaped even though selecting the referent's member does not expose the
pointer variable's own stack slot. Loop havoc replaces `h` with a fresh pointer;
the retained descriptor view still names the original address. A bounded state
probe confirms that the requested eight-byte read uses the fresh symbolic block
while the existing view covers the original external argument.

Recursing into the member's object expression instead preserves the carrier
while still tracking explicit address-taking nested there. On the recovery
branch this gets the reduction through its header, but opening `cells` then
fails with `kernel rejected checked resource unfold: the rewritten composite
is absent from both resource representations`. The original arena also passes
its former header failure and stops later at `arena_alloc` tactic 48,
`preserve` tactic 12, exhausting the unchanged 2,500,000-unit control budget.
Neither complete positive is restored. Keep these later failures visible;
this selective repair is not a full activation verdict.

All seven selected loop-carrier kernel tests pass, including the new stable-member
carrier and genuine escaped-slot controls. No full example-stage recheck is
claimed for this additional partial repair.
