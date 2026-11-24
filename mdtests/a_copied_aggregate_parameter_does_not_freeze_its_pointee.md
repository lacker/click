# Preserving a copied parameter binding does not preserve a mutated pointee

```c filename=aggregate_entry_write.c
struct packet { int32* data; };
void touch(struct packet input) { input.data[0] = 7; }
```

```click
verifying "aggregate_entry_write.c";
void touch(struct packet input) {
    owns input.data[0..1];
    requires input.data[0] == 3;
} by {
    have input.data[0] == 3 by { close(); }
    step_until(function.exit);
    have input.data[0] == 3 by { close(); }
}
```

```expect
fail: tactic 2: `have` failed
```
