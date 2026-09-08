# Generic proofs are checked without concrete clients

```click
theorem reflexive<T>(x: T) {
    ensures x == x by { normalize(); }
}

theorem via_generic<T>(x: T) {
    ensures x == x by { apply(reflexive(x)); }
}

theorem independent<T, U>(x: T, y: U) {
    ensures x == x by { apply(reflexive(x)); }
    ensures y == y by { apply(reflexive(y)); }
}

theorem list_law<T>(xs: List<T>, ys: List<T>, value: T) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) == 1 { 1 } else { list_contains(ys, value) } by {
        apply(list_contains_append(xs, ys, value));
    }
}

theorem nested<T>(xs: List<List<T>>) {
    ensures list_append(xs, List<List<T>>::Nil) == xs by {
        apply(list_append_right_identity(xs));
    }
}
```

```expect
pass
```
