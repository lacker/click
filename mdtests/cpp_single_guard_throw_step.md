# A single guarded throwing call must expose its cleanup as a step

This keeps one RAII object and one potentially throwing call. The proof does
not involve two-object ordering or cross-cell framing; it checks that the
call's normal and exceptional outcomes can each take one ordinary step for the
synthesized destructor before finishing.

```cpp filename=single_guard_step.cpp function=single_guard_step profile=scalar_int32
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

int single_guard_step(int& value, bool should_throw) {
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
verifying "single_guard_step.cpp";

void Restore_constructor(struct Restore* self, int32* slot) {
    owns &self->pointer;
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
    owns &self->pointer;
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

int32 single_guard_step(int32* value, bool should_throw) {
    owns value[0..1];
    ensures result == old(value[0]);
    ensures value[0] == old(value[0]);
} by {
    step();
    step();
    outcomes {
        returned {
            step();
            execute();
            simp();
        }
        threw {
            step();
            execute();
            simp();
        }
    }
}
```

```expect
pass
```
