# The driver proves theorem argument evaluation obligations

```click
theorem identity(value: int32) {
    ensures value == value by close();
}
theorem use_argument(x: int32) {
    requires 0 <= x;
    requires x < 10;
    ensures x == x by {
        apply(identity(x + 1));
        close();
    }
}
```

```expect
pass
```
