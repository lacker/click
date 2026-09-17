# An owning callback contract may be implemented by a narrower borrow

The named contract gives a callback two owned cells.  A read-only callback may
borrow just the first cell, without taking ownership of either cell.  The
ordinary resource algebra supplies that borrow from the named ownership.

```c filename=borrowed_callback_subrange.c
int32 read_first(int32* state) {
    return state[0];
}

int32 apply_read(int32 (*read)(int32*), int32* cells) {
    return read(cells);
}

int32 borrowed_subrange_caller(int32* cells) {
    return apply_read(&read_first, cells);
}
```

```click
verifying "borrowed_callback_subrange.c";

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

int32 borrowed_subrange_caller(int32* cells) {
    owns cells[0..2];
    ensures result == cells[0];
} by {
    execute();
    simp();
}
```

```expect
pass
```
