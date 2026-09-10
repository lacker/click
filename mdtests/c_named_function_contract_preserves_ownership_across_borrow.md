# Ownership survives an indirect borrowed callback call

The callback reads the first cell through a view.  After the indirect call,
the caller still owns both cells and may therefore mutate the second one.
This checks that callback refinement models a scoped borrow rather than
silently weakening the caller's owned resource.

```c filename=callback_borrow_preserves_ownership.c
int32 read_first(int32* state) {
    return state[0];
}

int32 apply_read(int32 (*read)(int32*), int32* cells) {
    return read(cells);
}

void borrow_then_write(int32* cells) {
    apply_read(&read_first, cells);
    cells[1] = 7;
}
```

```click
verifying "callback_borrow_preserves_ownership.c";

contract int32 ReadFirst(int32* cells) {
    owns cells[0..2];
    ensures result == cells[0];
}

int32 read_first(int32* state) {
    views state[0..1];
    ensures result == state[0];
} by {
    execute();
    simp();
}

int32 apply_read(int32 (*read)(int32*), int32* cells) {
    requires ReadFirst(read);
    owns cells[0..2];
    ensures result == cells[0];
} by {
    execute();
    simp();
}

void borrow_then_write(int32* cells) {
    owns cells[0..2];
    ensures cells[1] == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
