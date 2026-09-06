# A `uint64` field reads through `object()`

`object(p)` covers one complete struct. Its cells take the field types of
the layout, so an `unsigned long` field after an `int32` field reads back as
a 64-bit value rather than as int32 words.

```c filename=object_resource_uint64_field.c
struct node {
    int32 value;
    unsigned long word;
};

unsigned long read_word(struct node* node) {
    return node->word;
}
```

```click
verifying "object_resource_uint64_field.c";

unsigned long read_word(struct node* node) {
    requires node != 0;
    views object(node);
    ensures result == node->word;
} by {
    execute();
    simp();
}
```

```expect
pass
```
