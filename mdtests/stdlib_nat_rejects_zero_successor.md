# stdlib nat rejects zero successor

```click
theorem invalid(n: Nat) {
    ensures Nat::Zero == Nat::Succ(n) by close();
}
```

```expect
fail: invalid.ensures_0
```

