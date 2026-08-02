# opaque call old refers to call entry

This checks that a callee's `old(...)` postcondition is instantiated with the
memory state at the call boundary and remains usable by the caller.

```c filename=replace_cell.c
int32 replace_cell(int32 p[], int32 value) {
    int32 previous;
    previous = p[0];
    p[0] = value;
    return previous;
}
```

```c filename=replace_caller.c
int32 replace_caller(int32 p[], int32 value) {
    int32 previous;
    previous = replace_cell(p, value);
    return previous;
}
```

```click
verifying "replace_cell.c";
verifying "replace_caller.c";

int32 replace_cell(int32 p[], int32 value) {
    owns p[0..1] by auto;
    mutable p[0..1] by auto;
    ensures result == old(p[0]) by auto;
    ensures p[0] == value by auto;
}

int32 replace_caller(int32 p[], int32 value) {
    owns p[0..1] by auto;
    ensures result == old(p[0]) by auto;
}
```

```expect
pass
```
