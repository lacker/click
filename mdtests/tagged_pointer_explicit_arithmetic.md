# A tag equality closes by the simple `arithmetic using` step

The smart `simp` closure of a tagged-word equality expands to one explicit
`arithmetic() using` step naming the facts it used: the word's recorded
address form and the base alignment. Writing that step by hand checks the
same rule directly, with no search.

```c filename=tagged_pointer_explicit_arithmetic.c
struct node {
    int32 value;
    unsigned long word;
};

unsigned long set_black(unsigned long word, struct node* next) {
    return word | 2;
}
```

```click
verifying "tagged_pointer_explicit_arithmetic.c";

unsigned long set_black(unsigned long word, struct node* next) {
    requires aligned(next, 8);
    requires word == address(next) + 1;
    ensures result == address(next) + 3;
} by {
    execute();
    have result == address(next) + 3 by {
        arithmetic() using {
            word == address(next) + 1;
            aligned(next, 8);
        }
    }
    simp();
}
```

```expect
pass
```
