# Standard-library constructors check element types

```click
theorem wrong_element(pointer: int32*) {
    ensures List<int32>::Cons(pointer, List<int32>::Nil) == List<int32>::Nil by simp;
}
```

```expect
fail: expects
```
