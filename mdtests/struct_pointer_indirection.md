# Struct pointer-to-pointer indirection

Taking the address of a struct-pointer field produces a pointer-valued cell
that can be redirected and written through. The stored node pointer keeps its
provenance, and the update changes only the selected field cell.

```c filename=struct_pointer_indirection.c
struct node {
    int32 key;
    struct node* left;
    struct node* right;
};

int32 replace_left(struct node* root, struct node* replacement) {
    struct node** link = &root->left;
    *link = replacement;
    return (*link)->key;
}
```

```click
verifying "struct_pointer_indirection.c";

int32 replace_left(struct node* root, struct node* replacement) {
    requires loadable(root->left);
    requires loadable(replacement->key);
    consumes root->left;
    consumes replacement->key;
    mutable root->left;

    ensures result == replacement->key;
    ensures root->left == replacement;
    produces root->left;
    produces replacement->key;
} by auto;
```

```expect
pass
```
