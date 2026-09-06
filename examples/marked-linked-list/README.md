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
every tag operation the implementation performs is a checked rewrite on that
address form. `list_mark` sets the bit and refolds; `list_is_marked` reads it
through a mask; `list_next` clears the mask and casts back, recovering the
witness pointer and its provenance; `list_count_live` walks the list through
that cast; and `list_destroy` frees postorder. `list_prepend` stores a plain
tail address, and the fold infers the witness from that stored word.

Alignment is evidence, never an assumption from the pointee type. Fresh nodes
are aligned because the allocator says so, and the list interface states that
heads are 8-byte aligned so the tag bits below that alignment are free to use.

The example intentionally excludes loops over the list (the traversal is
recursive), shared tails, cycles, and concurrent access.
