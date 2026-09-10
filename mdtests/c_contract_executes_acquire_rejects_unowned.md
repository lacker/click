# A nonnull callback result does not supply ownership by itself

```click
resource Cell(p: int32*) { owns p[0..1]; }
contract int32* Nonnull() { ensures result != 0; }
contract int32* Owned() { ensures result != 0; produces Cell(result); }
theorem lift(acquire: int32* (*)()) executes acquire() {
    requires Nonnull(acquire);
    ensures Owned(acquire) by {
        step(Nonnull);
        fold(Cell(result));
        simp();
    }
}
```

```expect
fail: fold
```
