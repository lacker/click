# List equality preserves order

```click quick-solve
theorem reversed_is_not_equal() {
    ensures List<int32>::Cons(1, List<int32>::Cons(2, List<int32>::Nil))
        == List<int32>::Cons(2, List<int32>::Cons(1, List<int32>::Nil)) by close();
}
```

```expect
fail: `solve` failed
```
