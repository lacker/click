# `rbtree-insert` refuses a `contradiction` on `parent == 0`

The nightly example `examples/rbtree/rbtree-insert` fails on `master`
(`d421e24fd`). It is in `NIGHTLY` in `tests/examples.rs`, so the gate does not
run it.

## Reproduction

```sh
cargo build --bin click
target/debug/click verify examples/rbtree/rbtree-insert
```

```text
proof error:
  `contradiction(parent == 0)` requires an exact fact and its exact negation or opposite condition polarity
  `parent == 0` is available, but neither `not (parent == 0)` nor its opposite comparison is
```

The nightly examples `rbtree-erase` and `rbtree-augmented`, which import the
same model, also report `fold` refusals at this point
(`((load_uint64(p) & ~3) as (struct rb_node *)) == parent` and
`node->rb_right != node` not established). Those two have not been checked on
`master` separately.

## Violated invariant

A checked example proof keeps verifying. The proof at `rbtree_insert.click`
tactic 532 cites a fact that the current state no longer holds in the exact
polarity it names: either an earlier change dropped the `parent != 0` fact the
proof relied on, or the proof needs updating to state it.

## Acceptance criteria

- `click verify examples/rbtree/rbtree-insert` passes, with the C unchanged.
- The nightly example run passes for `rbtree-insert`, and the cause of the
  `rbtree-erase` and `rbtree-augmented` refusals is either fixed in the same
  change or filed separately.

## Progress after the explicit pointer proof repair

The initial null-parent contradictions now establish `parent != 0` by
rewriting `parent == cid` and using the unfolded context's `cid != 0`.
The root recoloring case states the masked parent-pointer fact explicitly.
Checked rewriting now rebuilds an integer-derived zero address as canonical
null, which lets that proof normalize
(`mdtests/a_rewritten_tagged_null_pointer_normalizes.md`). The two black-parent
branches also state the nonzero condition consumed by the C branch.
`rbtree_null_parent_helper_verifies` checks the unchanged C helper
that writes the tagged null parent; the C and contract are unchanged.

The full example still fails later, in the first rotation branch:

```text
`transport` found no frame evidence carrying its source fact to the target's state
source: at(before_grandparent_links,
    ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp)
target: ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp
```

The read is eight bytes at `gparent`. Its two framing walks cross seven and
seventeen memory steps, then reach the loop-effect state without proving
the queried bytes separate. The trace also contains the later pointer-field
stores and four-byte cells seeded by unfolding resources. Whether this is
another instance of
[`pointer-field-cells-are-cached-as-words-a-pointer-read-cannot-use.md`](pointer-field-cells-are-cached-as-words-a-pointer-read-cannot-use.md)
or needs an explicit frame premise is not yet established. Keep this report
open until the whole insertion example passes; the erase and augmented
reports remain open too.

## Reduced reconstructed-pointer transport defect

A small single-store reduction exposed a separate frame-checking defect:
`mdtests/a_word_pointer_fact_survives_a_store_through_an_alias.md`. The C store
writes `p->left`, with `p == g`; explicit separation proves it does not touch
`g->word`. Transport of a scalar fact about that word succeeds, but transport
of the pointer reconstructed from the word failed. The mask and loop were
not necessary to reproduce it.

The pointer frame crossed the store but compared its immediate pre-state with
the read's earlier named version. Cached field observations between those
states are not writes. The checker now uses the observation prefix's directly retained byte source
after that one checked transition. The reduced proof verifies and expands;
a scaling regression grows the observation chain and retains an overlapping
upper-half-write refusal.

This does not establish the full insertion proof. The original bare transport
at the first rotation still fails, and an explicit single-store transport in
that tree branch also remains refused. Rewriting a preserved numeric word alone
is insufficient: the reconstructed pointer also carries a read designation,
which scalar equality does not replace. Keep this report open while reducing
the remaining tree-specific frame failure.
