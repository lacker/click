# Logical choices remain independent of universal witnesses

```click
theorem independent_integer_choice() {
    requires exists (x: Integer) { x == 0 };
    ensures forall (arbitrary: Integer) {
        exists (found: Integer) { found == 0 and arbitrary == arbitrary }
    } by {
        intro();
        obtain (chosen: Integer) { chosen == 0 }
        have arbitrary == arbitrary by { normalize(); }
        witness { found: chosen };
        assumption();
    }
}
```

```expect
pass
```
