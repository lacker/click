# A bounded symbolic index reads an initialized aggregate parameter element

```c filename=aggregate_parameter_symbolic_index.c
struct inner { int32 value; };
struct packet { struct inner inner; int32 items[2]; int32* data; };
int32 indexed(struct packet input, int32 i) { return input.items[i]; }
```

```click
verifying "aggregate_parameter_symbolic_index.c";
int32 indexed(struct packet input, int32 i) {
    requires 0 <= i;
    requires i < 2;
    ensures result == input.items[i];
} by {
    if i == 0 {
        execute(); rewrite(i == 0); simp();
    } else {
        have 0 < i by { arithmetic() using { 0 <= i; i != 0; } }
        have i == 1 by { arithmetic() using { 0 < i; i < 2; } }
        execute(); rewrite(i == 1); simp();
    }
}
```

```expect
pass
```
