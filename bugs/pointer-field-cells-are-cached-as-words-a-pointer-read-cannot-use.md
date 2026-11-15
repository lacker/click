# Pointer field cells are cached as words a pointer read cannot use

Soundness: incomplete. Existing checked proofs are refused; nothing false is
accepted. Two reads of one unchanged pointer field get different names, so a
proof step that once closed by normalization is refused.

## Current status (2026-11-01)

The representation repair is implemented: composite unfolds observe complete
pointer cells, symbolic storage uses the same `LoadedPointer` identity as an
ordinary read, and same-source pointer observation runs preserve bytes in the
memory-history checker. The named-cell rule compares the full typed read,
including designation and extent. Scalar load handles no longer double as
pointer parameters in symbolic arrays.

Composite fields and ranges take their canonical typed observations from the
same selected naming state. Function-pointer fields retain their scalar
function-name carrier. These distinctions preserve callback entry assumptions,
repeated borrowed-resource unfolds, and nested reads used by transport proofs;
the existing full Markdown and example corpora cover those cases. Logical
pointer reads consult the selected state's complete cached observation
before following its byte identity, so a checked loop frame does not lose a
restored pointer value when observation-only states are skipped.

Regression coverage checks complete pointer cells, cached/ordinary read identity,
upper-half writes, wrong read provenance, and no-write witnesses for pointer
runs. The retained-field Markdown fixture also checks a bare before/after read
equality after unfolding, sibling stores, and a retaining call. Pointer-run
framing stays bounded as run sizes grow from 16 to 65,536 cells; observation
chains are checked at 8, 32, 128, and 512 cells. The pointer fact-stability audit
has zero differences before and after; its three quarantined fixture failures
are unchanged.

Keep this report open: the original sidecars do not yet meet the end-to-end
acceptance criteria. The initial repair `ca1d6dec0`, compared with the
pre-repair baseline `617ab6c8a`, gave these unchanged-production frontiers.
These long-running sidecars have not been rerun after the callback and
loop-cache follow-up:

| Sidecar | Before | After |
| --- | --- | --- |
| `rbtree_erase_augmented.click` | smart budget at line 544 | missing explicit `erase_spine_minimum` nonempty premise at line 596 |
| `rbtree_size_insert_context_double_far_rotation.click` | smart budget at line 191 | same |
| `rbtree_size_insert_mirrored_context_double_rotation.click` | fold argument equality at line 217 | earlier smart budget for `node->rb_left == 0` at line 203 |

No example proof or C source is changed by the representation repair. In a
scratch erase proof, explicitly normalizing the nonempty-constructor premise
passes line 596, then stops at an unavailable exact rewrite equality at original
line 652, still before the historical pointer-read trigger. The sections below
record the original investigation, not a claim that the full erase proof now
verifies.

## Original violated invariant

A read of a pointer field that no step writes has one name before and after a
call that does not touch it. Since #1806 every C pointer read is an 8-byte
`LoadedPointer` read. Unfolding a composite resource still caches each pointer
field as two 4-byte `Int32` words
(`materialize_composite_resource_cells_from_state` in
`src/surface/proof/resources.rs`: "Pointer fields keep the int32 words this
projection uses everywhere"). That rule fit the removed storage-relative
encoding, whose pointer read was a 4-byte word load. An 8-byte read cannot be
served from the two halves.

## Reproduction

`examples/rbtree/rbtree-erase/rbtree_erase_augmented.click` verified on master
`9415c258b` (just before #1806) and is refused on `1f9bde1fe`; the C and the
sidecar are unchanged:

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree/rbtree-erase/rbtree_erase_augmented.click
```

```text
`solve` failed for `__rb_erase_augmented.contract`
could not establish `child->rb_right == at(transplant, child->rb_right)`
```

The step is line 694, after `step(__rb_change_child(node, successor, tmp, root), ...)`.
Before #1806 both sides lowered to one term and `normalize()` closed it.

What happens:

- At `transplant`, the read of `child->rb_right` takes its name from the cell
  cached at unfold, named at the entry state.
- The call keeps `child->rb_right` in its retained frame. By design it forgets
  the cached cell (`CallHavocCellRule::KeptByCaller`), and a later load is named
  across the call edge.
- That naming walk (`cell_last_same_version_point`, assumption-free) reaches the
  pre-call state, finds only the two 4-byte halves, and keeps walking. It stops
  at the earlier store `rb_set_parent(tmp, successor)` through `node->rb_left`,
  which it cannot separate from `child + 8` without facts.

The kernel does prove the equality with facts. An explicit
`transport(at(transplant, child->rb_right) == at(transplant, child->rb_right), child->rb_right == at(transplant, child->rb_right)) using { };`
closes line 694. The same refusal then appears at line 738
(`have child->rb_right == at(transplant, child->rb_right) by solve();`
in current syntax; the recorded reproduction used the removed `auto()`).

The same cause probably explains two rbtree-augmented sidecars that already
failed before #1806 but now fail earlier:
`rbtree_size_insert_context_double_far_rotation.click` (a `solve` for
`node->rb_right == 0` at line 269, which `rewrite` plus `known` closed
before) and `rbtree_size_insert_mirrored_context_double_rotation.click`
(line 205). This is unconfirmed.

A small reduction (a store through `n->left`, then a call, then
`have child->right == at(before_call, child->right)`) passes on both
revisions; the trigger has not been isolated beyond the original proof.

## Attempted fix and what it exposed

Seeding a pointer field as one cell of the pointer type (in both the
struct-layout and the range branch of the function above) needs
`cell_value_is_exactly_load` in `src/kernel/proof/execution.rs` to accept a
pointer cell that holds the read its canonical load names. It still checks the
removed shape: same block, `Int32Scaled` load word. With both changes the lib
suite passes, but the corpus shows a spelling split:

- `symbolic_storage_cell_value` spells a pointer read as
  `Symbolic(load variable)` with the read as its designation; an ordinary load
  names it as the `LoadedPointer` itself.
- With whole pointer cells, the two spellings meet in one cell. Instance
  rewrite checking then fails with "the resource context is not the exchange
  its definition requires" (`mdtests/arena_prefix_free_reads_region_arena.md`,
  `mdtests/c_pointer_field_subrange_write_preserves_resources.md`, the arena
  example). An inner read in a range base's defining address is `Symbolic(v)`
  on one side and `LoadedPointer` on the other.
- `rbtree_erase_augmented.click` then stops earlier, at line 681 (`tmp == parent_model`).
- `mdtests/a_retained_pointer_field_fact_needs_its_listed_loop_alias.md`
  passes without its listed alias, which needs review before it is accepted.

The representation repair uses one spelling for a pointer read everywhere
(the `LoadedPointer` read), symbolic storage cells included, followed by whole
pointer cells. It also removes the obsolete pointer exclusion from the
same-source no-write rule: otherwise the newly complete cache entries are
mistaken for writes during transport. End-to-end proof work remains as listed
in the current status above.

## Acceptance criteria

- `rbtree_erase_augmented.click` verifies unchanged.
- An unfold caches a pointer field as one cell holding the read a load of it
  names, and the unfold naming check accepts exactly that value.
- A pointer read has one spelling, whatever produced its cell.
- `rbtree_size_insert_context_double_far_rotation.click` and
  `rbtree_size_insert_mirrored_context_double_rotation.click` fail no earlier
  than on `9415c258b`.
- A Markdown regression keeps the original pattern: a field cached by an
  unfold, a store through another pointer read, a call that retains the field,
  and a bare `have` equating the field's read before and after the call.
