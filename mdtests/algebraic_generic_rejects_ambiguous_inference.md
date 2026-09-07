# generic calls reject ambiguous type inference

A type parameter must be determined by the call arguments. Click does not
silently invent a logical type for an unconstrained instance.

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

function empty<T>() -> TestList<T> {
    TestList<T>::Nil
}

theorem ambiguous_empty() {
    ensures empty() == empty();
}
```

```expect
fail: cannot infer type argument T for function `empty`
```
