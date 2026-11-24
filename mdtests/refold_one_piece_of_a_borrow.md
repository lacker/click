# Refold one piece while another piece keeps the borrow live

```c filename=borrow.c
void pack(int *p);
void drop_first(int *p);

void update(int *p) {
    pack(p);
    drop_first(p);
    p[1] = 9;
}
```

```click
verifying "borrow.c";

resource pair(p: int32*) {
    views p[0..1];
    views p[1..2];
}

resource first(p: int32*) {
    views p[0..1];
}

extern void pack(int32 p[]) {
    views p[0..2] as input;
    produces pair(p) from input;
}

extern void drop_first(int32 p[]) {
    consumes first(p);
}

void update(int32 p[]) {
    owns p[0..2];
    ensures p[1] == 9;
} by {
    step();
    unfold(pair(p));
    fold(first(p));
    step();
    release_view(p[1..2]);
    step();
    step_until(function.exit);
    close();
}
```

```expect
pass
```
