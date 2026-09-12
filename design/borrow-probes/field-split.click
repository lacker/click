resource cell(n: struct node*) {
    owns n->value;
    owns n->next;
}

verifying "field-split.c";

void set_value(struct node* n, int32 v) {
    views n->next;
    owns n->value;
    ensures n->value == v;
} by {
    step();
    step();
    simp();
}

void caller(struct node* n) {
    owns cell(n);
    ensures n->next == old(n->next);
} by {
    step();
    fold(cell(n));
    step();
    simp();
}
