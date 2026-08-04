resource zero_list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        fact node->value == 0;
        contains zero_list(node->next);
    }
}

verifying "zero_list_empty.c";
verifying "zero_list_push.c";
verifying "zero_list_sum.c";
verifying "zero_list_sum_bounded.c";
verifying "zero_list_pipeline.c";

struct node* zero_list_empty() {
    produces zero_list(result);

    ensures result == 0;
} by {
    execute();
    fold(zero_list(result));
    simp();
}

int32 zero_list_push(struct node* node, struct node* tail) {
    requires node != 0;
    consumes node->value;
    consumes node->next;
    consumes zero_list(tail);
    mutable node->value, node->next;
    produces zero_list(node);

    ensures result == 0;
    ensures node->value == 0;
    ensures node->next == tail;
} by {
    execute();
    fold(zero_list(node));
    frame();
    simp();
}

int32 zero_list_sum(struct node* node) {
    requires node != 0;
    views zero_list(node);
    immutable;

    ensures result == 0;
} by {
    observe(zero_list(node));
    if node->next == 0 {
        execute();
        frame();
        simp();
    } else {
        execute();
        frame();
        simp();
    }
}

int32 zero_list_sum_bounded(struct node* node, int32 fuel) {
    decreases fuel;
    requires node != 0;
    views zero_list(node);
    immutable;

    ensures result == 0;
} by {
    observe(zero_list(node));
    if fuel > 0 {
        if node->next == 0 {
            execute();
            frame();
            simp();
        } else {
            execute();
            frame();
            simp();
        }
    } else {
        execute();
        frame();
        simp();
    }
}

int32 zero_list_pipeline(struct node* first, struct node* second) {
    requires first != 0;
    requires second != 0;
    consumes first->value;
    consumes first->next;
    consumes second->value;
    consumes second->next;
    mutable first->value, first->next, second->value, second->next;
    produces zero_list(first);

    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    fold(zero_list(second->next));
    fold(zero_list(second));
    step();
    step();
    fold(zero_list(first));
    execute();
    frame();
    simp();
}
