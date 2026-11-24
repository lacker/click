# Old keeps the entry value after a private field write

```c filename=old_aggregate_field_rejects_current_value.c
struct packet { int32* data; };
void redirect(struct packet input, int32* q) { input.data = q; }
```

```click
verifying "old_aggregate_field_rejects_current_value.c";
void redirect(struct packet input, int32* q) {
    requires input.data != q;
    ensures q == old(q);
} by {
    step();
    have input.data == q by { normalize(); }
    have old(input.data) == q by { close(); }
}
```

```expect
fail: could not establish `old(input->data) == q`
```
