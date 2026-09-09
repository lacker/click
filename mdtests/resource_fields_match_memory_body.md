# Constructor-selected named-instance memory

A resource match is declarative. Constructor evidence selects one arm; it
does not create an instance or split the proof.

```c filename=resource_fields_match_memory_body.c
int32 read_some(int32* p, int32 expected) { return *p; }
int32 read_none(int32* p) { return 0; }
```

```click
verifying "resource_fields_match_memory_body.c";

spec enum Maybe<T> { None, Some(T) }

resource cell(p: int32*) {
    field model: Maybe<int32>;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => {
            owns p[0..1];
            fact p[0] == value;
        },
    }
}

int32 read_some(int32* p, int32 expected) {
    owns c: cell(p);
    requires c.model == Maybe<int32>::Some(expected);
    ensures result == expected;
    ensures c.model == old(c.model);
} by {
    unfold(c);
    execute();
    fold(c);
    simp();
}

int32 read_none(int32* p) {
    owns c: cell(p);
    requires c.model == Maybe<int32>::None;
    ensures p == 0;
    ensures result == 0;
    ensures c.model == old(c.model);
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
