# composite resource for a struct-owned buffer

This checks the conservative "struct owns buffer" pattern. The abstract
resource takes both the owner object and the buffer as explicit parameters,
then ties the owner field to a fact. This avoids depending on an initial
symbolic pointer load from an owner field.

```c filename=set_owned_first.c
struct owner {
    int32 len;
};

int32 set_owned_first(struct owner* owner, int32 data[]) {
    data[0] = owner->len;
    return data[0];
}
```

```click
resource owned_one_cell(owner: struct owner*, data: int32*) {
    contains write(owner->len);
    contains write(data[0..1]);
    fact owner->len == 1;
}

verifying "set_owned_first.c";

int32 set_owned_first(struct owner* owner, int32 data[]) {
    requires separate(memory(owner[0..1]), memory(data[0..1]));
    requires owned_one_cell(owner, data);

    ensures owned_one_cell(owner, data) by {
        unfold(owned_one_cell(owner, data));
        symbolic_execute();
        fold(owned_one_cell(owner, data));
    }

    ensures result == 1 by {
        unfold(owned_one_cell(owner, data));
        symbolic_execute();
        fold(owned_one_cell(owner, data));
        simp();
    }
}
```

```expect
pass
```
