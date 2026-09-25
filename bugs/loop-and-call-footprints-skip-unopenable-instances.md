# Loop and call footprints skip instances they cannot open

## Violated invariant

A loop that declares a resource, and a call whose contract owns one, may
write any memory that resource owns. The kernel summarizes that write set
as the resource's owned footprint (`checked_owned_memory_ranges` in
`src/kernel/functions.rs`) and havocs it, so a fact about a cell inside the
footprint cannot be transported across the loop or call unchanged.

The footprint is computed by opening the held resources. Since `a18ec5c0`
it opens a field-bearing instance one body layer at its own fields and
counts an iterated ownership fact as the span of every element it could
hold. It still contributes nothing for a resource it cannot open from one
state:

- a matched body whose arm is not decided in the current state;
- a recursive body, or a body that binds an existential witness;
- an instance nested deeper than `OWNED_FOOTPRINT_INSTANCE_DEPTH` (8); and
- a recursive composite the expansion leaves folded.

A loop or call holding such a resource is therefore summarized as writing
none of its memory. A `transport` of a fact about a cell that resource owns
succeeds across the loop or call, and the proof can conclude a value the
loop body or callee has overwritten. This is the same defect the two
regressions landed with `a18ec5c0` prove for the field-bearing and iterated
cases (`mdtests/loop_binder_instance_footprint_includes_its_memory.md`,
`mdtests/call_through_instance_footprint_includes_its_memory.md`), left open
for these shapes. The gap is recorded in the doc comment above
`OWNED_FOOTPRINT_INSTANCE_DEPTH` and in
`docs/internals/resource-tracker.md`.

Making these shapes fail closed (treat an unopenable resource as writing all
memory it could reach) was tried and breaks about seven example projects,
because their proofs transport facts across calls that hold recursive
composites which the callee does not in fact write. So the fix has to be
precise, not merely conservative.

## Intended regression

For each unopenable shape, a small program whose loop or callee holds the
resource and overwrites a cell it owns, with a proof that transports the
cell's entry value across the loop or call and claims it in the
postcondition. Each must be refused at the transport. Suggested shapes:

- a recursive list resource held by a loop that walks the list and writes
  every node's `value`; postcondition `head->value == old(head->value)`;
- a resource with `let w: struct node* where ...` held by a callee that
  writes through the witness;
- a matched resource whose arm is decided only inside the callee, which
  writes a cell the arm owns;
- an instance nested nine layers deep, if the depth bound survives the fix.

Each fixture must prove a false postcondition on the kernel at `1b428d5b`.

## Acceptance criteria

- The footprint of a held resource covers every cell any of its arms, its
  recursive unfoldings, or its witness-bound bodies may own, computed
  symbolically from the definition (for example, the declared memory
  clauses over the definition's parameters and fields, with a recursive
  body contributing the span its arguments can reach) rather than by
  enumerating unfoldings; or, where a precise footprint is not computable,
  the loop or call is refused with a diagnostic naming the resource and the
  shape, never silently summarized as writing nothing.
- The seven example projects that rely on transporting facts across calls
  holding recursive composites keep verifying, with their proofs unchanged
  or with an explicit, documented step where the callee's footprint really
  includes the transported cell.
- The regressions above are in the gate as expect-fail fixtures, the
  positive controls (the same programs where the loop or callee does not
  write the cell) pass, and a four-size deterministic work test shows the
  footprint computation is linear in the definition, not in the number of
  unfoldings.
- `docs/internals/resource-tracker.md` and the `OWNED_FOOTPRINT_INSTANCE_DEPTH`
  comment no longer describe the gap as open. `scripts/check.sh` passes.
  Delete this file and its list entries when the fix, its regressions, and
  the documentation land.
