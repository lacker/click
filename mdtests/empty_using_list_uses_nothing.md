# an empty using list uses nothing

`using { }` is accepted wherever a list is, and means the tactic uses no
premises. That differs from leaving `using` off: `close()` would find the
precondition below in the context, while `close() using { }` may not use it.

```click
theorem empty_using_uses_nothing(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by {
        close() using { };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
