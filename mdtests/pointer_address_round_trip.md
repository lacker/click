# A pointer survives a round trip through `unsigned long`

Casting an object pointer to `unsigned long` yields its address term, which
keeps the exact source pointer. Storing that word in a struct field, loading
it back, and casting to the pointer type recovers the original pointer with
its provenance, so the recovered pointer can be dereferenced and compared.

```c filename=pointer_address_round_trip.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* stash_and_recover(struct node* node, struct node* next) {
    node->word = (unsigned long)next;
    return (struct node*)node->word;
}

int32 read_through_word(struct node* node, struct node* next) {
    node->word = (unsigned long)next;
    return ((struct node*)node->word)->value;
}
```

```click
verifying "pointer_address_round_trip.c";

struct node* stash_and_recover(struct node* node, struct node* next) {
    requires node != 0;
    owns node->word;
    mutable node->word;
    ensures result == next;
    ensures node->word == address(next);
} by {
    execute();
    frame();
    simp();
}

int32 read_through_word(struct node* node, struct node* next) {
    requires node != 0;
    requires next != 0;
    owns node->word;
    views next->value;
    mutable node->word;
    ensures result == next->value;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
