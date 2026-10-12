# Null pointer rewrites compose with unsigned address arithmetic

Rewriting a pointer to null must produce the same integer address as a C cast,
including beneath arithmetic with a symbolic other operand. The masked form
is the parent/color tag equation used when folding a replacement rbtree root.

```click
theorem null_address_add_left(p: int32*, x: uint64) {
    requires p == 0;
    ensures address(p) + x == x by { rewrite(p == 0); normalize(); }
}
theorem null_address_add_right(p: int32*, x: uint64) {
    requires p == 0;
    ensures x + address(p) == x by { rewrite(p == 0); normalize(); }
}
theorem null_parent_tag(p: int32*, word: uint64) {
    requires p == 0;
    ensures address(p) + (word & 1) == (word & 1) by {
        rewrite(p == 0); normalize();
    }
}
```

```expect
pass
```
