# A borrowed segment is returned as it was lent

`push` owns the one cell at the current length and the length field itself,
and views the data pointer. The body writes the cell and then advances the
length. An `owns` clause is a borrow: what the function returns is exactly
what it was lent, so the returned cell is the one at the length the caller
saw, not the cell at the length the body wrote. Reading the clause at exit
would have asked the function to return a cell it never held.

```c filename=borrowed_window_returns_what_was_lent.c
struct buffer {
    int32 len;
    int32* data;
};

void push(struct buffer* owner, int32 value) {
    owner->data[owner->len] = value;
    owner->len = owner->len + 1;
}
```

```click
verifying "borrowed_window_returns_what_was_lent.c";

void push(struct buffer* owner, int32 value) {
    requires 0 <= owner->len;
    requires owner->len < 1000;
    requires separate(memory(object(owner)), memory((owner->data + owner->len)[0..1]));
    views owner->data;
    owns owner->len;
    owns (owner->data + owner->len)[0..1];
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data == old(owner->data);
    ensures owner->data[old(owner->len)] == value;
} by auto;
```

```expect
pass
```
