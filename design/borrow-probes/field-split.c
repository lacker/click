struct node {
    int32 value;
    struct node* next;
};

void set_value(struct node* n, int32 v) {
    n->value = v;
}

void caller(struct node* n) {
    set_value(n, 7);
}
