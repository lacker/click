# An Integer disequality does not give a wrapping word disequality

`u + 1 != 0` holds of the Integer `u + 1`, which is `4294967296` for
`u == 4294967295`; the `uint32` word `(u + 1) as uint32` is `0` there.
`solve` proves a word disequality from an Integer one only where the word
equality forces the Integer equality, so it refuses this one.

```click quick-solve
theorem wrapping_word(u: uint32) {
    requires u + 1 != 0;
    ensures ((u + 1) as uint32) != 0 by {
        close();
    }
}
```

```expect
fail: could not establish `((u + 1) as uint32) != 0`
```
