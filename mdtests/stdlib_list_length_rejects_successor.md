# stdlib list length rejects successor

```click
theorem invalid<T>(xs: List<T>, ys: List<T>) {
    ensures list_length(list_append(xs, ys)) == Nat::Succ(nat_add(list_length(xs), list_length(ys))) by {
        apply(list_length_append(xs, ys));
        normalize();
    }
}
```

```expect
fail: invalid.ensures_0
```

