# List equality preserves order

```click
theorem reversed_is_not_equal() {
    ensures List<int32>::Cons(1, List<int32>::Cons(2, List<int32>::Nil))
        == List<int32>::Cons(2, List<int32>::Cons(1, List<int32>::Nil)) by simp;
}
```

```expect
fail: `simp` failed
```
