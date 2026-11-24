# A theorem's nonempty premise cannot be dropped for Empty

```click
spec enum Tree { Empty, Node(int32), }

theorem nonempty(child: Tree) {
    requires not(child == Tree::Empty);
    ensures not(child == Tree::Empty) by close();
}

theorem empty_is_not_nonempty() {
    ensures not(Tree::Empty == Tree::Empty) by {
        apply(nonempty(Tree::Empty));
        close();
    }
}
```

```expect
fail: theorem `nonempty` has an unproved obligation
```
