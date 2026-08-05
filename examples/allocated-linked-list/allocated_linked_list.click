resource allocated_list(node: struct node*) {
    if node != 0 {
        contains allocation(node, sizeof(struct node));
        owns object(node);
        contains allocated_list(node->next);
    }
}

verifying "list_empty.c";
verifying "list_prepend.c";
verifying "list_head.c";
verifying "list_drop_front.c";
verifying "list_destroy.c";
verifying "list_pipeline.c";

struct node* list_empty() {
    produces allocated_list(result);

    ensures result == 0;
} by {
    execute();
    fold(allocated_list(result));
    simp();
}

struct node* list_prepend(int32 value, struct node* tail) {
    consumes allocated_list(tail);
    produces allocated_list(result);

    ensures result == tail or result != 0;
    ensures result != tail implies result->value == value;
    ensures result != tail implies result->next == tail;
} by {
    execute();
    if result == tail {
        simp();
    } else {
        fold(allocated_list(result));
        simp();
    }
}

int32 list_head(struct node* node) {
    requires node != 0;
    views allocated_list(node);
    immutable;

    ensures result == node->value;
} by {
    observe(allocated_list(node));
    execute();
    frame();
    simp();
}

struct node* list_drop_front(struct node* node) {
    requires node != 0;
    consumes allocated_list(node);
    produces allocated_list(result);

    ensures result == old(node->next);
} by {
    unfold(allocated_list(node));
    execute();
    simp();
}

void list_destroy(struct node* node) {
    decreases resource allocated_list(node);
    consumes allocated_list(node);
} by {
    if node == 0 {
        unfold(allocated_list(node));
        execute();
        simp();
    } else {
        unfold(allocated_list(node));
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
