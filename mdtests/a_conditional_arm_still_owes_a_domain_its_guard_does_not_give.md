# A conditional arm still owes a domain its guard does not give

Scoping an arm under its guard does not drop its obligation: the arm selected
by `64u64 <= s` shifts by the width or more, so the conditional is refused
where it is stated.

```click
theorem unguarded(a: uint64, s: uint64) {
    ensures (if 64u64 <= s { a << s } else { 0u64 }) == 0u64 by {
        close();
    }
}
```

```expect
fail: it denotes a value only where 1 condition of its evaluation holds
```
