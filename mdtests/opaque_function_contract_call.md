# opaque function contracts execute as one step

This checks that a verified callee contract, rather than its C body, supplies
the resource transition and memory postcondition used by its caller.

```c filename=set_cell.c
int32 set_cell(int32 p[], int32 value) {
    p[0] = value;
    return value;
}
```

```c filename=set_then_read.c
int32 set_then_read(int32 p[], int32 value) {
    int32 ignored;
    ignored = set_cell(p, value);
    return p[0];
}
```

```click
verifying "set_cell.c";
verifying "set_then_read.c";

int32 set_cell(int32 p[], int32 value) {
    owns p[0..1] by auto;
    mutable p[0..1] by frame;
    ensures p[0] == value by auto;
    ensures result == value by auto;
}

int32 set_then_read(int32 p[], int32 value) {
    owns p[0..1] by {
        execute_step();
        execute_step();
        execute_step();
    }
    ensures result == value by {
        execute_step();
        execute_step();
        execute_step();
        simp();
    }
}
```

```expect
pass
```
