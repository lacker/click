# Widening identities precede reassociation

```click quick-solve
theorem bridge(a: uint32, b: uint32) {
    ensures to_integer(a) + to_integer(b) + -30 == (to_integer(a as int64) + to_integer(b as int64)) - to_integer(30i64) by {
        have to_integer(a as int64) == to_integer(a) by close();
        have to_integer(b as int64) == to_integer(b) by close();
        rewrite(to_integer(a as int64), to_integer(a));
        rewrite(to_integer(b as int64), to_integer(b));
        close() using {};

    }
}
```

```expect
pass
```
