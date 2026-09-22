# Historical pointee values survive both free and parameter exit

```c filename=aggregate_parameter_old_pointee.c
struct packet { int32* data; };
void dispose(struct packet input) { free(input.data); }
```

```click
verifying "aggregate_parameter_old_pointee.c";
resource cell(p: int32*) {
    contains allocation(p, 4);
    owns p[0..1];
}
void dispose(struct packet input) {
    consumes cell(input.data);
    requires input.data[0] == 7;
    ensures old(input.data[0]) == 7;
} by { unfold(cell(input.data)); execute(); simp(); }
```

```expect
pass
```
