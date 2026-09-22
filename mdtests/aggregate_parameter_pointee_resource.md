# Logical parameter fields preserve values without preserving C storage

```c filename=aggregate_parameter_pointee_resource.c
struct inner { int32 value; };
struct packet { struct inner inner; int32 items[2]; int32* data; };

int32 touch(struct packet input) { input.data[0] = 7; return input.data[0]; }
```

```click
verifying "aggregate_parameter_pointee_resource.c";
resource data_cell(p: int32*) { owns p[0..1]; }
int32 touch(struct packet input) {
    consumes data_cell(input.data);
    requires input.data[0] == 3;
    produces data_cell(input.data);
    ensures result == 7;
    ensures input.data[0] == 7;
    ensures old(input.data[0]) == 3;
} by { unfold(data_cell(input.data)); execute(); fold(data_cell(input.data)); simp(); }

```

```expect
pass
```
