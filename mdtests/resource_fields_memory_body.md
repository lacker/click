# Unchanged fields through an owned memory body

Unfolding exposes the immediate memory and its relation to arbitrary symbolic
fields. Folding after C returns must restore ownership with those fields intact.

```c filename=resource_fields_memory_body.c
int32 read(int32* p) { return *p; }
```

```click
verifying "resource_fields_memory_body.c";

spec enum Mark { Clear, Set }

resource cell(p: int32*) {
    field value: int32;
    field mark: Mark;
    owns p[0..1];
    fact p[0] == value;
}

int32 read(int32* p) {
    owns c: cell(p);
    ensures result == c.value;
    ensures c.value == old(c.value);
    ensures c.mark == old(c.mark);
} by {
    unfold(c);
    execute();
    fold(c);
    simp();
}
```

```expect
pass
```
