# Positional witness values retain their binder types

```click quick-solve
theorem positional(n: int32, m: Integer, p: int32*) {
    ensures answer: exists (first: int32*, second: Integer, third: int32) {
        first == p and second == m and third == n
    } by {
        witness(p, m, n);
        close();
    }
}
```

```expect
pass
```
