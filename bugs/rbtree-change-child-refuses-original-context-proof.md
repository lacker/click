# The original rbtree context helper refuses its first branch

Priority: P1.

Soundness: incomplete. The unchanged `__rb_change_child` program and its
committed context-resource proof are refused with invalid memory access at
`branch`. No false acceptance is known. This also prevents the missing-link
mutation tests from exercising their intended obligations.

## Reproduction

On the PR #646 branch after merging upstream master `e3a830768`, verify
[`examples/rbtree-erase/rbtree_change_child.click`](../examples/rbtree-erase/rbtree_change_child.click)
against its unchanged `rb_erase_augmented.c` input and imported
[`rbtree_resources.click`](../examples/rbtree-model/rbtree_resources.click):

```sh
cargo run --bin click -- verify examples/rbtree-erase/rbtree_change_child.click
```

The refusal is:

```text
`__rb_change_child.contract` tactic 0: `branch` could not evaluate the C condition because it has undefined behavior: invalid memory access
```

The proof selects `before.model`, establishes the relation of `parent` to the
selected context, and unfolds the owned context before executing the C branch.
The `Top` context owns `root->rb_node`; the left and right contexts own their
identity's parent/color and child fields. The helper performs no integer-to-
pointer conversion. Do not classify this refusal as the deferred integer-origin
contract feature or relax the native access checks to bypass it.

The existing tests `rbtree_change_child_requires_left_link`,
`rbtree_change_child_requires_right_link`, and
`rbtree_change_child_requires_root_link` in
[`tests/examples.rs`](../tests/examples.rs) likewise fail their diagnostic
assertions at this earlier branch refusal. A private probe adding typed-place
requirements for the live parent and root did not repair the positive proof;
that probe was removed, and the original source and contract remain unchanged.

## Acceptance criteria

- Reduce and identify the lost read/ownership evidence or invalid condition
  evaluation, using the original context-match/unfold/branch pattern.
- Verify the unchanged positive helper for top, left and right contexts.
- Restore mutation coverage at the intended missing child/root link, preserving
  the original C and rejecting both absent permissions and wrong updates.
- Check expansion and fresh/retained rechecking of the positive proof, without
  deriving pointer provenance from numeric equality.
