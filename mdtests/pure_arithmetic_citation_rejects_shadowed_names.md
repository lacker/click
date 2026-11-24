# A retained arithmetic citation keeps its binding scope

A checked outer `have` cannot supply a fact about the fresh universal variable
introduced under the same written name.

```click
theorem retained_citation(n: int32) {
    requires 0 <= n;
    ensures 0 <= n by {
        have 0 <= n by close();
        close();
    }
}
theorem shadowed_citation(n: int32) {
    requires 0 <= n;
    ensures forall (n: int32) { 0 <= n } by {
        have 0 <= n by close();
        intro();
        normalize() using { 0 <= n; };
    }
}
```

```expect
fail: not exactly available
```
