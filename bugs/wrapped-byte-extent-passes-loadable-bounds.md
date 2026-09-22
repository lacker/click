# The loadable byte-offset route certifies a wrapped goal extent

P1. An extent compared by a signed bound must carry its own non-wrap
premise; a residue is not a count.

## What was found

`proves_loadable_region_from_range`
(`src/kernel/assumptions/memory_reasoning.rs:916`) certifies a goal region
from a smaller fact region. Its byte-offset route (lines 933-943) checks
`0 <= byte_offset` and `byte_offset + bytes <= range_bytes`, where
`access_end = Bitvector32Term::add(byte_offset, bytes)` is a modular 32-bit
add compared by `signed_less_equal`. A goal extent of `0x60000000` bytes at
a `0x20000000` byte offset wraps its end into `0x80000000` (signed `INT_MIN`);
the comparison passes while the true byte end is 1.5 GiB past the range.

Machine-confirmed:
`hunt_investigation_wrapped_byte_extent_reads_as_in_bounds`
(`src/kernel/assumptions/memory_reasoning.rs` investigation module): a goal
`loadable(arr + 0x20000000, 0x60000000)` is certified from a 16-byte region
under an empty fact context.

The element-granularity routes in the same rule family demand
`assumed_extent_covers_its_element_count` (the guarded lines), and the
documented trap of exactly this class lives one file over
(`mdtests/wrapped_viewable_extent_is_not_a_cell.md` and
`assumed_range_is_a_valid_byte_extent`): the byte-offset arms and
`proves_loadable_region_from_structural_range`'s constant branch
(memory_reasoning.rs:589) plus
`proves_loadable_cell_from_region`'s constant-width branch (997) skip the
goal-extent premise on the byte routes.

The same residue-signing class also rides in
`loadable_covered_by_fact` (`src/kernel/api/contract_certification.rs:300`,
already covered by
`bugs/byte-extent-residue-compare-certifies-wrapped-loads.md`) — the fix
should share one deciding helper: a byte-extent comparison refuses any
`access_end` whose 32-bit word needs a wrap to stay inside the range
(window form `0 <= end`, `end <= span` over exact `i64` bytes or a bounded
word), and the shared guarded premise keeps both routes consistent.

## Intended regression

The investigation test as a true regression: the wrapped goal extent must be
*refused* by `proves_loadable_region_from_range`, plus the byte-offset
window boundary (exact in-bounds goal still certified).

## Acceptance

- [ ] The byte-offset routes carry the goal-extent validity premise at the
      deciding line; the wrapped-extent regression refuses.
- [ ] `scripts/check.sh` green.
