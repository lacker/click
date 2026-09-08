# Acquired ownership does not authorize reading another pointer

```c filename=wrong_pointer.c
int32* read_wrong(int32* (*acquire)(), int32* value, int32* other) {
    int32* cell = acquire();
    if (cell != 0) {
        *value = *other;
    }
    return cell;
}
```

```click
resource Cell(p: int32*) { owns p[0..1]; }
resource MaybeCell(p: int32*) { if p != 0 { owns Cell(p); } }
contract int32* Boxed() { immutable; produces MaybeCell(result); }

verifying "wrong_pointer.c";
int32* read_wrong(int32* (*acquire)(), int32* value, int32* other) {
    requires Boxed(acquire);
    owns value[0..1];
    mutable value[0..1];
    produces MaybeCell(result);
} by {
    step(); step(Boxed);
    if c(cell) != 0 {
        unfold(MaybeCell(c(cell)));
        unfold(Cell(c(cell)));
        execute();
        fold(Cell(result)); fold(MaybeCell(result)); frame(); simp();
    } else {
        unfold(MaybeCell(c(cell)));
        execute();
        fold(MaybeCell(result)); frame(); simp();
    }
}
```

```expect
fail: missing resource fact
```
