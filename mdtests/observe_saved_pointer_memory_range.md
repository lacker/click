# Observe an explicitly selected saved-pointer memory range

The descriptor saves the pointer value, while observation establishes viewability
in the current state. The local write does not require a history search.

```c filename=observe_saved.c
struct box { int* data; };
struct byte_box { unsigned char* data; };
void update(struct box* box) { int scratch; scratch = 1; }
void update_byte(struct byte_box* box) { int scratch; scratch = 1; }
int update_bounds(struct box* box, int n) {
    int count;
    count = n;
    count = 1;
    return count;
}
```

```click
verifying "observe_saved.c";
void update(struct box* box) {
    owns *box;
    owns box->data[0..2];
    ensures viewable(memory(at(function.entry, box->data)[0..2]));
} by {
    step_until(function.exit);
    observe(at(function.entry, box->data)[0..2]);
    close();
}
void update_byte(struct byte_box* box) {
    owns *box;
    owns box->data[0..2];
    ensures viewable(memory(at(function.entry, box->data)[0..2]));
} by {
    step_until(function.exit);
    observe(old(box->data)[0..2]);
    close();
}
int32 update_bounds(struct box* box, int32 n) {
    requires 1 < n;
    owns *box;
    owns box->data[0..n];
    ensures viewable(at(function.entry, memory(box->data[0..n])));
} by {
    step();
    step();
    mark saved;
    step();
    step_until(function.exit);
    have at(saved, count) == n by { close(); }
    observe(at(saved, memory(box->data[0..count])));
    have viewable(at(function.entry, memory(box->data[0..n]))) by { close(); }
    close();
}
```

```expect
pass
```
