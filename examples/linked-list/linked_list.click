resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        contains list(node->next);
    }
}

verifying "list_empty.c";
verifying "list_head.c";
verifying "list_push_front.c";
verifying "list_pop_front.c";
verifying "list_roundtrip.c";

struct node* list_empty() {
    produces list(result);

    ensures result == 0;
} by {
    execute();
    fold(list(result));
    simp();
}

int32 list_head(struct node* node) {
    requires node != 0;
    owns list(node);
    immutable;

    ensures result == node->value;
} by {
    unfold(list(node));
    execute();
    fold(list(node));
    frame();
    simp();
}

int32 list_push_front(
    struct node* node,
    int32 value,
    struct node* tail
) {
    requires node != 0;
    consumes node->value;
    consumes node->next;
    consumes list(tail);
    mutable node->value, node->next;
    produces list(node);

    ensures result == value;
    ensures node->value == value;
    ensures node->next == tail;
} by {
    execute();
    fold(list(node));
    frame();
    simp();
}

int32 list_pop_front(
    struct node* node
) {
    requires node != 0;
    consumes list(node);
    produces node->value;
    produces node->next;
    produces list(node->next);

    ensures result == old(node->value);
    ensures node->next == old(node->next);
    ensures node->value == old(node->value);
} by {
    unfold(list(node));
    execute();
    simp();
}

int32 list_roundtrip(
    struct node* node,
    int32 value,
    struct node* tail
) {
    requires node != 0;
    consumes node->value;
    consumes node->next;
    owns list(tail);
    mutable node->value, node->next;
    produces node->value;
    produces node->next;

    ensures result == value;
    ensures node->next == tail;
} by {
    execute();
    frame();
    simp();
}
