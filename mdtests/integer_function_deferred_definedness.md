# Deferred Integer calls retain C argument definedness

```click
function f(x: int32) -> Integer {
    to_integer(x)
}

theorem missing_guard(x: int32) {
    ensures f(x + 1) == f(x + 1) by {
        simp();
    }
}

theorem guarded(x: int32) {
    requires defined(x + 1);
    ensures f(x + 1) == f(x + 1) by {
        simp();
    }
}
```

```expect
fail: defined
```
