# C++ guard cleanup on a caught cross-call exception

The constructor changes a referenced cell, and the destructor restores it.
The guard is local to the `try` block, so both a normal helper return and its
`int` exception must destroy the guard before the caller observes the cell.
The constructor's separation postcondition records the real object invariant
needed by the destructor; no proof-only change to the C++ source is required.

```cpp filename=guarded.cpp function=guarded profile=scalar_int32
struct Restore {
    int* pointer;
    int saved;

    explicit Restore(int* slot) noexcept : pointer(slot), saved(*slot) {
        *pointer = 9;
    }

    ~Restore() noexcept { *pointer = saved; }
};

int helper(bool should_throw) {
    if (should_throw) { throw 7; }
    return 5;
}

int guarded(int& value, bool should_throw) {
    try {
        Restore guard(&value);
        helper(should_throw);
    } catch (int caught) {
        return value;
    }
    return value;
}
```

```click
verifying "guarded.cpp";

void Restore_constructor(struct Restore* self, int32* slot) {
    owns self->pointer;
    owns self->saved;
    owns slot[0..1];
    ensures self->pointer == slot;
    ensures self->saved == old(slot[0]);
    ensures slot[0] == 9;
    ensures separate(memory(object(self)), memory(self->pointer[0..1]));
} by {
    execute();
    simp();
}

void Restore_destructor(struct Restore* self) {
    requires separate(memory(object(self)), memory(self->pointer[0..1]));
    owns self->pointer;
    owns self->saved;
    owns self->pointer[0..1];
    ensures self->pointer == old(self->pointer);
    ensures self->saved == old(self->saved);
    ensures self->pointer[0] == old(self->saved);
} by {
    execute();
    simp();
}

int32 helper(bool should_throw) throws int32 {
    ensures result == 5;
    exceptional ensures exception == 7;
}

int32 guarded(int32* value, bool should_throw) {
    owns value[0..1];
    ensures result == old(value[0]);
    ensures value[0] == old(value[0]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
