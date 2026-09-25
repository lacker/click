# a refused `have` in a pure theorem names the premises it actually consulted

The order facts used to narrow a viewable range are absent. The explicit
`viewable(p[hi - 1..hi])` claim must fail and report the premises in scope.
Logical reads can still be named without establishing this range claim.

```click
theorem last_cell(p: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures lo < hi by {
        have viewable(p[hi - 1..hi]) by { simp(); }
        assumption();
    }
}
```

```expect
fail: narrowing that range needs `lo <= (hi - 1)`
```
