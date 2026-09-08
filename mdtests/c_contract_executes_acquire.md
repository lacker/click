# A callback returns ownership only when acquisition succeeds

The callback may return null. A nonnull result carries an owned cell;
the refinement packages its raw ownership as a `Cell`. The ordinary caller
checks the result before reading into a separately owned output cell, and
returns the acquired ownership to its caller. No allocation freshness is assumed.

```c filename=acquire.c
int32* read_acquired(int32* (*acquire)(), int32* value) {
    int32* cell = acquire();
    if (cell != 0) {
        *value = *cell;
    }
    return cell;
}
```

```click
resource MaybeRaw(p: int32*) {
    if p != 0 {
        owns p[0..1];
    }
}
resource Cell(p: int32*) {
    owns p[0..1];
}
resource MaybeCell(p: int32*) {
    if p != 0 { owns Cell(p); }
}
contract int32* Raw() {
    immutable;
    produces MaybeRaw(result);
}
contract int32* Boxed() {
    immutable;
    produces MaybeCell(result);
}
theorem lift(acquire: int32* (*)()) executes acquire() {
    requires Raw(acquire);
    ensures Boxed(acquire) by {
        step(Raw);
        if result != 0 {
            unfold(MaybeRaw(result));
            fold(Cell(result));
            fold(MaybeCell(result));
            frame(); simp();
        } else {
            unfold(MaybeRaw(result));
            fold(MaybeCell(result));
            frame(); simp();
        }
    }
}
verifying "acquire.c";
int32* read_acquired(int32* (*acquire)(), int32* value) {
    requires Raw(acquire);
    owns value[0..1];
    mutable value[0..1];
    produces MaybeCell(result);
    ensures result != 0 implies value[0] == result[0];
    ensures result == 0 implies value[0] == old(value[0]);
} by {
    apply(lift(acquire));
    step();
    step(Boxed);
    if c(cell) != 0 {
        unfold(MaybeCell(c(cell)));
        unfold(Cell(c(cell)));
        execute();
        fold(Cell(result));
        fold(MaybeCell(result));
        frame(); simp();
    } else {
        unfold(MaybeCell(c(cell)));
        execute();
        fold(MaybeCell(result));
        frame(); simp();
    }
}
```

```expect
pass
```
