# Returned ownership does not prove allocation freshness

An allocation resource authorizes access and deallocation; it does not say
that the block was created during this caller. Initializing the returned cell
therefore cannot promise that all entry memory was unchanged. Keep this C
unchanged as a rejection test, separate from the ownership/read example.

```c filename=acquire.c
int32* initialize_acquired(int32* (*acquire)()) {
    int32* cell = acquire();
    if (cell != 0) {
        *cell = 7;
    }
    return cell;
}
```

```click
resource MaybeRaw(p: int32*) {
    if p != 0 {
        contains allocation(p, sizeof(int32));
        owns p[0..1];
    }
}
resource Cell(p: int32*) {
    contains allocation(p, sizeof(int32));
    owns p[0..1];
}
resource MaybeCell(p: int32*) {
    if p != 0 { owns Cell(p); }
}
resource MaybeInitialized(p: int32*) {
    if p != 0 {
        contains allocation(p, sizeof(int32));
        owns p[0..1];
        fact p[0] == 7;
    }
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
int32* initialize_acquired(int32* (*acquire)()) {
    requires Raw(acquire);
    immutable;
    produces MaybeInitialized(result);
} by {
    apply(lift(acquire));
    step();
    step(Boxed);
    if c(cell) != 0 {
        unfold(MaybeCell(c(cell)));
        unfold(Cell(c(cell)));
        execute();
        fold(MaybeInitialized(result));
        frame(); simp();
    } else {
        unfold(MaybeCell(c(cell)));
        execute();
        fold(MaybeInitialized(result));
        frame(); simp();
    }
}
```

```expect
fail: unverified claims: Effect(0)
```
