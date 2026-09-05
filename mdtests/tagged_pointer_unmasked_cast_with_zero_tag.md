# An unmasked cast back needs the tag proven zero, by any evidence

`rb_red_parent` casts the raw word back with no mask, relying on redness
meaning the color bit is clear. The obligation is that the tag is zero, and
a precondition on the tag discharges it.

```c filename=tagged_pointer_unmasked_cast_with_zero_tag.c
struct node {
    int32 value;
    unsigned long word;
};

int32 red_parent_is(unsigned long word, struct node* next, uint64 color) {
    return (struct node*)word == next;
}
```

```click
verifying "tagged_pointer_unmasked_cast_with_zero_tag.c";

int32 red_parent_is(unsigned long word, struct node* next, uint64 color) {
    requires word == address(next) + color;
    requires color == 0;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
