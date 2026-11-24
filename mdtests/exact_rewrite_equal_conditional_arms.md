# Exact rewrites can give conditionals identical arms

```click
theorem equal_word_arms(flag: Bool, n: Integer, m: Integer) {
    requires n == m;
    requires -2147483648 <= n and n <= 2147483647;
    requires -2147483648 <= m and m <= 2147483647;
    ensures to_integer(if flag { to_int32(n) } else { to_int32(m) }) == to_integer(to_int32(m)) by {
        rewrite(n, m);
        close();
    }
}

theorem equal_bool_arms(flag: Bool, n: Integer, m: Integer) {
    requires flag;
    requires n == m;
    ensures (if flag { if n < 0 { true } else { false } } else { if m < 0 { true } else { false } }) == (if m < 0 { true } else { false }) by {
        rewrite(n, m);
        close();
    }
}
```

```expect
pass
```
