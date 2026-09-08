# An established nonnull guard also permits post-call unfolding

No proof case is necessary when the source contract establishes the guard.

```click
resource MaybeCell(p: int32*) {
    if p != 0 { owns p[0..1]; fact p[0] == 7; }
}
resource Cell(p: int32*) { owns p[0..1]; fact p[0] == 7; }
contract int32* Raw() {
    immutable;
    ensures result != 0;
    produces MaybeCell(result);
}
contract int32* Boxed() {
    immutable;
    ensures result != 0;
    ensures result[0] == 7;
    produces Cell(result);
}
theorem lift(acquire: int32* (*)()) executes acquire() {
    requires Raw(acquire);
    ensures Boxed(acquire) by {
        step(Raw);
        unfold(MaybeCell(result));
        fold(Cell(result));
        frame(); simp();
    }
}
```

```expect
pass
```
