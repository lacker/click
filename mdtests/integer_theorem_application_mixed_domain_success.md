# Integer theorem applications can carry C and Integer parameters together

```click
theorem mixed(i: Integer, m: int32) {
    requires i == 0;
    requires m == m;
    ensures m == m by { simp(); }
}

theorem use_mixed(i: Integer, m: int32) {
    requires i == 0;
    requires m == m;
    ensures m == m by {
        apply(mixed(i, m));
    }
}
```

```expect
pass
```
