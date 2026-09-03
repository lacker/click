# induction does not accept a captured quantified fact

The inner universal binder is intentionally named `y`, the same identity that
the surrounding theorem goal uses. A checked `intro` must freshen it rather
than let the available induction fact prove a different proposition.

```click
theorem capture(n: int32) {
    requires n >= 0;
    ensures forall (x: int32) { x == 5 implies forall (y: int32) { y == 5 } }
    by {
        induct(n) as ih;
        intro();
        intro();
        have forall (z: int32) { z == 5 } by {
            intro();
            assumption();
        }
        assumption();
    }
}
```

```expect
fail: assumption
```
