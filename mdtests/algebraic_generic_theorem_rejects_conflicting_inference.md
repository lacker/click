# generic theorem applications reject conflicting type arguments

```click
theorem first_is_reflexive<T>(left: T, right: T) {
    ensures left == left by simp;
}

theorem conflicting(left: int32, right: int32*) {
    ensures left == left by {
        apply(first_is_reflexive(left, right));
        assumption();
    }
}
```

```expect
fail: cannot infer type arguments for theorem `first_is_reflexive`: type parameter `T` is both int32 and int32*
```
