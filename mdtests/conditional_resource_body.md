# conditional resource body

A resource body can be active or empty according to a load-free condition over
its parameters. The condition must be decided before `fold` or `unfold` uses
the body.

```c filename=conditional_resource_body.c
int32 set_if_present(int32* p) {
    *p = 7;
    return *p;
}
```

```c filename=conditional_resource_empty.c
int32 empty_value(int32* p) {
    return 0;
}
```

```click
resource maybe_cell(p: int32*) {
    if p != 0 {
        owns p[0..1];
    }
}

verifying "conditional_resource_body.c";
verifying "conditional_resource_empty.c";

int32 set_if_present(int32* p) {
    requires p != 0;
    owns maybe_cell(p);
    mutable p[0..1];

    ensures result == 7;
} by {
    unfold(maybe_cell(p));
    execute();
    fold(maybe_cell(p));
    frame();
    simp();
}

int32 empty_value(int32* p) {
    requires p == 0;
    owns maybe_cell(p);
    immutable;

    ensures result == 0;
} by {
    unfold(maybe_cell(p));
    execute();
    fold(maybe_cell(p));
    frame();
    simp();
}
```

```expect
pass
```
