# A tag equality closes by an explicit special arithmetic certificate

The typed special certificate names the word's recorded address form and the
base alignment directly, with no search.

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
        arithmetic_certificate special {
            premise 0: word == address(next) + 1 => word == address(next) + 1;
            premise 1: aligned(next, 8) => aligned(next, 8);
            pointer_word_equality relation 0 alignments [1] => result == address(next) + 3;
            conclusion 0;
        }
    }
    simp();
}
```

```expect
pass
```
