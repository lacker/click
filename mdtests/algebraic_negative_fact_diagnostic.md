# Negated algebraic facts do not dump their type schemas

```click
theorem impossible(xs: List<List<int32>>, ys: List<List<int32>>) {
    requires not(xs == ys);
    ensures 0 == 1;
}
```

```expect
fail: not (algebraic value equality)
```
