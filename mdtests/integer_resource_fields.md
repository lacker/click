# Integer resource model fields

A mathematical resource field preserves its exact symbolic value across an
unchanged C function. It has no C storage location.

```c filename=integer_resource_fields.c
int32 identity(int32 value) { return value; }
void create() { }
void change() { }
```

```click
verifying "integer_resource_fields.c";

resource account() {
    field total: Integer;
    fact total >= 0;
}

int32 identity(int32 value) {
    owns model: account();
    ensures result == value;
    ensures model.total == old(model.total);
} by {
    execute();
    simp();
}

void create() {
    produces model: account();
    ensures model.total == 18446744073709551616;
} by {
    execute();
    let model = fold(account(), { total: 18446744073709551616 });
    simp();
}

void change() {
    owns model: account();
    requires model.total == 18446744073709551616;
    ensures model.total == 18446744073709551617;
    ensures old(model.total) == 18446744073709551616;
} by {
    unfold(model);
    execute();
    let model = fold(account(), { total: 18446744073709551617 });
    simp();
}
```

```expect
pass
```
