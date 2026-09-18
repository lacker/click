# Load-variable naming is not stable across the surface and kernel

## Status

Open. Found during the arena parameterization work while trying to unfold a
region resource whose body loads through a two-level pointer. This is an
independent tooling defect, not an arena modeling problem: the same shape
fails for any resource with the same clauses. It blocks
[arena-resource-ownership.md](arena-resource-ownership.md) because the arena's
`arena_region`/`arena_metadata` shape reproduces it.

## Violated invariant

A load variable's id is documented as content-addressed: "the id is derived
deterministically ... every pass -- contract-grant lowering, requirement
evaluation, and body execution -- writes the same load with the same variable
without sharing any allocator state, and certificates check across runs"
(`load_variable_for_cell` in `src/kernel/eval/memory_loads.rs`). An `unfold`
names the cells it exposes through this function, and the kernel independently
recomputes the name in `memory_only_adds_named_cells`
(`src/kernel/proof/execution.rs`) to check the rewrite. Those two
recomputations must agree for the same `(memory, pointer)`.

They do not. The id is `hash(canonical_epoch, pointer)`, where
`cell_epoch_for_load_variable` (`src/kernel/memory_provenance.rs`) walks the
memory DAG crossing store edges it can prove disjoint. That walk consults a
`PureFactContext`, so the canonical epoch -- and therefore the id -- is a
function of the ambient assumptions, not of the memory alone. The surface
materializes cells with the proof's accumulated facts and a partially built
memory; the kernel recomputes with the pre-rewrite snapshot and an empty
context. Different proof power stops the walk at different snapshots, so the
same cell gets two ids.

This is the tension: the epoch walk needs assumptions to cross unrelated
stores (that is what lets a body fact survive a sibling write), while the id
contract requires assumption-independence. This shape is where they collide.

## Evidence

Instrumented run on the repro below: the added cell holds
`Variable(2174969270483)`, while `memory_only_adds_named_cells` recomputes
`Variable(2184814315594)`. `cell_epoch_for_load_variable` on the checker's
base memory returns a different epoch than the materializer reached, and
recomputing with the materializer's (already-built) memory returns the
materializer's value. So the divergence is the epoch, not the pointer or the
snapshot content.

## Intended regression

A valid unfold must verify. Every clause below is load-bearing; each removal
was verified to pass.

```c filename=load_variable_epoch_unfold.c
struct arena {
    int32* data;
    int32 capacity;
};

struct region {
    struct arena* arena;
};

int32 f(struct region* r, struct arena* out) {
    return 0;
}
```

```click
spec enum Tag { T(int32) }

resource part(r: struct region*) {
    field tag: Tag;
    match tag {
        Tag::T(x) => {
            owns r->arena;
            owns r->arena->data;
            owns r->arena->capacity;
            owns r->arena->data[x..r->arena->capacity];
        },
    }
}

verifying "load_variable_epoch_unfold.c";

int32 f(struct region* r, struct arena* out) {
    owns b: part(r);
    consumes object(out);
    ensures result == 0;
} by {
    match b.tag {
        Tag::T(x) => {
            unfold(b);
            execute();
            let b = fold(part(r), { tag: Tag::T(x) });
            simp();
        },
    }
}
```

```expect
pass
```

Current output at `unfold(b)`:

```text
an unfold may only name cells it exposes, but it added a cell at Pointer { .. }
that is not the canonical load of its own pointer at the pre-rewrite snapshot
```

Load-bearing clauses (removing any makes it pass):

- `consumes object(out)` where `out` has the same struct type as the resource's
  owned object. `views` and `owns` reproduce equally; a differently typed
  object, a differently shaped object, or no clause all pass. This is the
  oddest requirement and follows from the epoch walk resolving to an ancestor
  that the unrelated object's memory reaches differently.
- Two levels of indirection (`r->arena->data`). One level passes.
- A range endpoint that is a payload-indexed or pointer-loaded term
  (`data[x..capacity]`). Constant endpoints and `[0..capacity]` pass.
- At least two cells materialized under the loaded base pointer.

The `fold`/`execute` are not required: `unfold(b)` alone reproduces.

## Acceptance criteria

- The regression above verifies, and is added as an un-quarantined mdtest.
- The fix keeps the sibling-write framing the epoch walk exists for: existing
  regressions such as `mdtests/rb_child_load_identity_across_unfold.md` and
  `mdtests/rb_replace_node_with_children.md` stay green.
- `scripts/check.sh` passes.

## Open design question

The id contract says content-addressed; the walk needs assumptions. A fix must
choose one:

- make the checker's recomputation use the same proof power as the
  materializer (thread the same `PureFactContext` into
  `memory_only_adds_named_cells`), leaving the id contract as-is; or
- make the id genuinely assumption-free and move whatever disjointness the
  walk needs into the memory DAG itself.

The first is smaller and appears sufficient from the instrumentation; the
second is the principled reading of the documented contract. Determine which
before implementing.
