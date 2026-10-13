# Marked Linked List

A singly linked list whose `next` field is an `unsigned long` word carrying
the tail pointer with the low bit as a deletion mark. This is the sequential
half of the Harris lock-free list and the same shape as allocator and
collector mark bits, and it is exactly how Linux `rb_node` packs its parent
pointer and color.

The `marked_list(node)` resource owns each node and its allocation, records
that the node is 8-byte aligned, and binds the tail as an existential witness:
`let next: struct node* where aligned(next, 8) and node->word == address(next)
+ (node->word & 1)`. The word is the tail's address plus its own low bit, so
the model currently records only numeric relationships. `list_prepend` stores
a plain tail address and its checked fold preserves the existing child resource;
the empty-list and prepend constructors verify.

The original full project is an active rejection control for
[`integer-pointer-origin-contracts-design.md`](../../issues/integer-pointer-origin-contracts-design.md).
`list_next` clears the mask and casts back, but a numeric witness equation does
not promise the retained pointer origin required by that cast. The project must
refuse at that operation, rather than fail in construction or silently restore
provenance from equal bits. Positive modular traversal and destruction coverage
returns when the shared origin-contract mechanism is implemented. `list_mark`
sets the bit and refolds, and `list_is_marked` observes the bit; neither operation
alone supplies the missing origin promise.

Alignment is evidence, never an assumption from the pointee type. Fresh nodes
are aligned because the allocator says so, and the list interface states that
heads are 8-byte aligned so the tag bits below that alignment are free to use.

The example intentionally excludes loops over the list (the traversal is
recursive), shared tails, cycles, and concurrent access.
