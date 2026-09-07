# generic calls reject ambiguous type inference

A type parameter must be determined by the call arguments. Click does not
silently invent a logical type for an unconstrained instance.

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

function empty<T>() -> List<T> {
    List<T>::Nil
}

theorem ambiguous_empty() {
    ensures empty() == empty();
}
```

```expect
fail: cannot infer type argument T for function `empty`
```
