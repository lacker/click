verifying "rbtree_size_copy.c";

resource size_metadata(node: struct rb_node*) {
    field value: int32;
    owns ((struct sized_node*)(void*)node)->size;
    fact ((struct sized_node*)(void*)node)->size == value;
}

void sized_copy(struct rb_node* rb_old, struct rb_node* rb_new) {
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    ensures source.value == old(source.value);
    ensures target.value == old(source.value);
} by {
    unfold(source);
    unfold(target);
    execute();
    fold(source);
    let target = fold(size_metadata(rb_new), { value: old(source.value) });
    simp();
}

contract CopySize(source: size_metadata(rb_old), target: size_metadata(rb_new))
    for void(struct rb_node* rb_old, struct rb_node* rb_new) {
    owns source;
    owns target;
    ensures source.value == old(source.value);
    ensures target.value == old(source.value);
}

theorem sized_copy_has_size_contract()
    executes sized_copy(struct rb_node* rb_old, struct rb_node* rb_new) {
    ensures CopySize(&sized_copy) as { source: s, target: t } by {
        step(sized_copy(rb_old, rb_new), { source: s, target: t });
        simp();
    }
}
