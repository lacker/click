# A constructor field takes an exact widening

Every `int32` is an `int64`, so `x: int32` converts to `Seq<int64>`'s
`int64` field without a cast, and a claim about the result holds of the
widened value. The constructor `Seq::Cons(x, Seq::Nil)` leaves its type
argument to inference, which takes it from the function's return type
before its arguments, so the body is a `Seq<int64>`. Before, inference
fixed `Seq<int32>` from `x` and the body was refused, and the explicit
`Seq<int64>::Cons(x, ...)` type-checked but lowered to no path.

```click quick-solve
spec enum Seq<T> {
    Nil,
    Cons(T, Seq<T>),
}

function wrap(x: int32) -> Seq<int64> {
    Seq::Cons(x, Seq::Nil)
}

function wrap_let(x: int32) -> Seq<int64> {
    let wrapped: Seq<int64> = Seq::Cons(x, Seq::Nil);
    wrapped
}

theorem wrapped(x: int32) {
    ensures wrap(x) == Seq<int64>::Cons(x, Seq<int64>::Nil) by {
        unfold(wrap(x));
        close();
    }
}
```

```expect
pass
```
