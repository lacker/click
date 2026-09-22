# Logical parameter fields preserve values without preserving C storage

```c filename=aggregate_parameter_pointee_contract.c
struct inner { int32 value; };
struct packet { struct inner inner; int32 items[2]; int32* data; };

int32 touch(struct packet input) { input.data[0] = 7; return input.data[0]; }
```

```click
verifying "aggregate_parameter_pointee_contract.c";
int32 touch(struct packet input) {
    consumes input.data[0..1];
    requires input.data[0] == 3;
    produces input.data[0..1];
    ensures result == 7;
    ensures input.data[0] == 7;
    ensures old(input.data[0]) == 3;
} by { execute(); simp(); }

```

```expect
pass
```
