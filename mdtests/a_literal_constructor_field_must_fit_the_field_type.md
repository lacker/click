# A literal constructor field must fit the field's type

A literal constructor argument is a value of its field's type. `300` is no
`int8`, so `Seq<int8>::Cons(300, ...)` is refused where it is read, rather
than wrapped to 44 or reported as lowering to no path.

```click
spec enum Seq<T> {
    Nil,
    Cons(T, Seq<T>),
}

theorem out_of_range() {
    ensures not (Seq<int8>::Cons(300, Seq<int8>::Nil) == Seq<int8>::Nil) by {
        close();
    }
}
```

```expect
fail: the literal `300` is not a value of field type `int8` of `Cons`
```
