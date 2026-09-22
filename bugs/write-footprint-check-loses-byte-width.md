# The storage-footprint check loses the write's byte width

P1. "Write inside the owned footprint" is a byte-interval question; an
address question is not substitute (used `access_byte_overlap` discipline).

## What was found

`storage_writes_outside_owned_footprint`
(`src/kernel/functions.rs:5294-5307`) decides a hard-error refusal
(`src/surface/verification.rs:2804`) about whether an own check's write
stays inside the function's owned footprint. Its input collects the write
set through `collect_memory_effect_write_pointers`
(`src/kernel/reasoning/memory_resolution.rs:2478`), which maps each
`(pointer, bytes)` pair down to the bare `pointer`, and the containment
checks (`pointer_in_memory_range_shallow_with_facts` and
`pointer_in_range_by_shallow_fact_graph_with_width`) decide membership of
the start *address* — the `width` argument there is the owned range's own
element width, not the write's. A two-byte write anchored inside the
footprint's last byte crosses the boundary and is classified `covered`.

Route: the write's `bytes` are carried through the effect facts and then
dropped at exactly the deciding check; the byte-interval rules elsewhere
reach the conclusion through `access_byte_overlap` (`memory_resolution.rs`),
and this rule re-derives by address alone.

## Minimal C

```c
uint8_t owned[4]; static uint8_t *neighbor;
/* contract: owns owned@0[0..4];  ... *(uint16_t *)&owned[3] = 1; */
```

The write covers `owned[3]` and one byte beyond the footprint; the
address-conservative rule reports it in-bounds.

## Intended regression

Keep `(pointer, bytes)` end-to-end into the footprint rule; the negative
regression asserts the wide write at the footprint's last byte is refused
as outside, and (if the refusals manufacturers earlier elsewhere) the
test pins which layer decides by bytes.

## Acceptance

- [ ] The footprint check decides on byte intervals, with the
      partial-overlap-interval regression refusing.
- [ ] `scripts/check.sh` green.
