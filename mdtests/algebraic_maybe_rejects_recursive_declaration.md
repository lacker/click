# recursive algebraic declarations remain explicit future work

```click
spec enum List<T> {
    Nil,
    Cons(T, List),
}

theorem placeholder() {
    ensures 0 == 0 by simp;
}
```

```expect
fail: recursive algebraic datatype field `List::Cons` is not supported in the nonrecursive first slice
```
