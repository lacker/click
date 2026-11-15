# Whole-array assignments and borrowed states

`arrays.rs` and `arrays.click` preserve `rust-array-values` byte for byte.
All sixteen existing contracts now verify through Charon. Whole-array reference
assignments use the checked compact array-region operation; its immutable
source state supports shared external reads and mutable external writes.
Copies retain their bytes after either source or destination changes.
Constructor operand order, call side effects (including zero repeats), and
argument and assignment order remain covered by the frozen fixture.

`bounds.rs` covers local reference assignment, repeated fill, self-copy,
independent states, and empty arrays. `external.rs` adds borrowed copies and
fills at 8, 1024, and million elements, signed states after mutation, byte
copies, and empty borrowed arrays. False-byte assertions fail. `verify`,
`profile`, `audit`, and expanded certificates recheck the same contracts.
Live tests re-extract the checkpoints and the unchanged parity suite, retaining
compiler rejection of shared-reference writes and conflicting mutable borrows.

The kernel captures represented source runs and sparse cells, then retains one
compact state run for the unknown remainder. MemoryState forwarding avoids
expanding MIR's temporary array copies. Source selection uses persistent
address ranges, including symbolic bases, rather than scanning unrelated
parameter cells. Deterministic kernel regressions check storage, work,
variable collection, unchanged mappings, single-source-load substitution,
source/destination stem cancellation, overlap, neighbors, and sparse states.
The existing local adapter scaling regressions retain bounded lowered code.

Full source read and destination write authority are required. Destination
read-only qualifiers and active view loans remain protected. Alignment,
known bounds, and automatic-storage initialization are checked. Empty arrays
perform no memory access but still require correctly typed operands. Supported
elements are `i32`, `u8`, and `u32`; accepted external pointers are argument or
object storage with constant or single scaled 32-bit bases. Live heap storage,
typed union overlays, and general symbolic pointer expressions remain outside
this compact path. By-value array parameters and aggregate returns remain
separate adapter gaps.

The external scalar-array profile milestone extends the semantic profile and updates
checkpoint identities. Compiler pins, extraction flags, and previous ULLBC
bytes are unchanged. External Charon locks require explicit refresh.

```sh
scripts/check.sh --charon-live
cargo nextest run --lib --test rust_import -E 'test(external_array_) | test(charon_array_) | test(charon_external_array_)'
```

Current fixture parity is 10/16 (62.5%) fully verified, 14/16 (87.5%) importing:
two normalization gaps and four proof-observation gaps remain. The
[loop-header checkpoint](../loop-headers/README.md) closes the next two import
gaps. Complete parity before switching the default and retiring legacy extraction.

Compact external writes require a whole-footprint decision for existing possibly
aliasing runs. If separation cannot be checked compactly, they refuse promptly
rather than traversing the logical array extent.
