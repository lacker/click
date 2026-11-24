# generic theorem applications require inferable type arguments

```click
theorem hidden<T>(value: int32) {
    ensures value == value by close();
}

theorem use_hidden(value: int32) {
    ensures value == value by {
        apply(hidden(value));
        close();
    }
}
```

```expect
fail: cannot infer type argument T for theorem `hidden`
```
