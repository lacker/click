# an empty view authorizes nothing

`views p[0..0]` names no bytes. It is a well-formed requirement — the caller
has nothing to hand over — but it is not a licence to read `p[0]`, and it is
not evidence that `p` points anywhere at all.

Here the callee declares the empty view and then loads `p[0]` anyway. The
read has no authority behind it, so the call is rejected rather than
discharged by the view clause merely being present.

```c filename=empty_view_authorizes_nothing.c
int32 head(int32* p) {
    return p[0];
}

int32 empty_view_authorizes_nothing() {
    int32 cell[1];
    cell[0] = 7;
    return head(cell);
}
```

```click
verifying "empty_view_authorizes_nothing.c";

int32 head(int32* p) {
    views p[0..0];
    ensures result == p[0];
}

int32 empty_view_authorizes_nothing() {
    ensures result == 7;
}
```

```expect
fail: missing resource fact `views p[0..1]`
```
