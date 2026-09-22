# A union store leaves the other members' typed overlays stale

P1. A store to one member invalidates every other member's previous value;
an overlay keyed by the member type must not outlive that fact.

## What was found

`store_union` (`src/kernel/primitives/memory_state.rs:2512`) replaces only
the `(pointer, value_type)` overlay it is handed and removes the raw cell.
Every other member's typed overlay at the same address survives, and the
load layer answers `known_union_value(pointer, that_type)` as the typed
value — the pre-store bytes — where every concrete C execution reads the
last store's bytes. Machine-confirmed on
`claude/soundness-hunt-phase2b`:
`hunt_investigation_union_store_of_one_member_leaves_the_other_stale`
(`src/kernel/primitives/memory_state.rs` investigation module) — after
`store_union(u, UInt8, 0xAA)` followed by `store_union(u, Int32, 0x51)`,
`known_union_value(u, UInt8)` still answers `0xAA`.

The scalar path pays the same debt by construction —
`without_field_cells` ("leaving the destination's own cells would read back
as its previous contents", `memory_state.rs` doc) and the copy arm in
`src/kernel/functions.rs:11209-11216` — but no union counterpart exists:
`copy_aggregate_fields`' union loop (`functions.rs:11333`) `continue`s when
`copy_aggregate_union_member` cannot carry a member, leaving the
destination's stale overlay in place. The load resolver's
`known_union_value` route is authoritative ("the authoritative view for an
exact typed load"), so nothing downstream re-derives the staleness.

## Intended regression

The investigation test as a true regression plus its C-level shape
(`union U { long a; unsigned char b; }; u.b = 0xAA; u.a = 0x51;` — a later
`u.b` read must not answer `0xAA`): a typed overlay store must invalidate
every other member's overlay at the same address, or the read layer must
refuse a member whose overlay predates the last store of any other member.

## Acceptance

- [ ] After a union member store, no other member's typed overlay at that
      address answers with its pre-store value (refused or dropped).
- [ ] `scripts/check.sh` green.
