resource marked_list(node: struct node*) {
    if node != 0 {
        contains allocation(node, sizeof(struct node));
        owns object(node);
        fact aligned(node, 8);
        let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
        contains marked_list(next);
    }
}

verifying "list_empty.c";
verifying "list_prepend.c";
verifying "list_mark.c";
verifying "list_is_marked.c";
verifying "list_next.c";
verifying "list_count_live.c";
verifying "list_destroy.c";
verifying "list_pipeline.c";

struct node* list_empty() {
    produces marked_list(result);

    ensures result == 0;
    ensures aligned(result, 8);
} by {
    execute();
    fold(marked_list(result));
    simp();
}

struct node* list_prepend(int32 value, struct node* tail) {
    requires aligned(tail, 8);
    consumes marked_list(tail);
    produces marked_list(result);

    ensures result == tail or result != 0;
    ensures aligned(result, 8);
} by {
    execute();
    if result == tail {
        simp();
    } else {
        fold(marked_list(result));
        simp();
    }
}

void list_mark(struct node* node) {
    requires node != 0;
    owns marked_list(node);

    ensures (node->word & 1) != 0;
} by {
    unfold(marked_list(node));
    execute();
    fold(marked_list(node));
    simp();
}

int32 list_is_marked(struct node* node) {
    requires node != 0;
    views marked_list(node);
    immutable;

    ensures result == 0 or result == 1;
} by {
    observe(marked_list(node));
    execute();
    frame();
    simp();
}

struct node* list_next(struct node* node) {
    requires node != 0;
    views marked_list(node);
    immutable;

    ensures address(result) == (node->word & ~1);
    ensures aligned(result, 8);
} by {
    observe(marked_list(node));
    execute();
    frame();
    simp();
}

uint32 list_count_live(struct node* node) {
    decreases resource marked_list(node);
    owns marked_list(node);
} by {
    if node == 0 {
        execute();
        simp();
    } else {
        unfold(marked_list(node));
        execute();
        fold(marked_list(node));
        simp();
    }
}

void list_destroy(struct node* node) {
    decreases resource marked_list(node);
    consumes marked_list(node);
} by {
    if node == 0 {
        unfold(marked_list(node));
        execute();
        simp();
    } else {
        unfold(marked_list(node));
        execute();
        simp();
    }
}

int32 list_pipeline(int32 first, int32 second) {
    ensures result == 0;
} by {
    execute();
    simp();
}
