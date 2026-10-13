# Opening machine existentials preserves the exact types

```click
theorem opened_wide() {
    requires exists (x: int64) { x == 4294967296i64 };
    ensures exists (y: int64) { y == 4294967296i64 } by {
        obtain (candidate: int64) { candidate == 4294967296i64 }
        witness { y: candidate };
        simp();
    }
}

theorem opened_byte() {
    requires exists (x: uint8) { x == 'a' };
    ensures exists (y: uint8) { y == 'a' } by {
        obtain (candidate: uint8) { candidate == 'a' }
        witness { y: candidate };
        simp();
    }
}
```

```expect
pass
```
