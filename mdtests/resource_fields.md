# Resource field declarations

Fields describe pure abstract state, not extra C storage. A resource may
declare several typed fields before its body clauses. Merely declaring a
field does not establish its value or grant an owned resource instance.

```c filename=resource_fields.c
int32 identity(int32 value) {
    return value;
}
```

```click
verifying "resource_fields.c";

spec enum Mark {
    Clear,
    Set,
}

resource buffer(p: int32*, capacity: int32) {
    field contents: List<int32>;
    field mark: Mark;
    field revision: int32;
    owns p[0..capacity];
}

resource nested(p: int32*) {
    field contents: List<List<int32>>;
    owns p[0..1];
}

abstract resource credit();

int32 identity(int32 value) {
    owns 2 of credit();
    ensures result == value;
} by {
    execute();
    simp();
}

theorem ordinary_pure_law(x: int32) {
    ensures x == x by { simp(); }
}
```

```expect
pass
```

This checks declarations only. [Named instance bindings](resource_instance_bindings.md)
cover symbolic field projections. Opening bodies and establishing fields
against memory remain unsupported.
