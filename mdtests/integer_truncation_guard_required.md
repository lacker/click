# A symbolic divisor needs its nonzero guard

```click
theorem bad(a: Integer, b: Integer) {
    ensures truncating_remainder(a, b) == truncating_remainder(a, b) by close();
}
```

```expect
fail: it denotes a value only where 1 condition of its evaluation holds
```
