# Negated algebraic facts do not dump their type schemas

```click
theorem impossible(xs: List<List<int32>>, ys: List<List<int32>>) {
    requires not(xs == ys);
    ensures 0 == 1;
}
```

```expect
fail: recent premises (showing 1 of 1):
    internal (no exact Click spelling): ¬(value A:List = value B:List)
```
