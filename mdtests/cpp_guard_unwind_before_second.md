# C++ cleanup before a later guard is constructed

The first guard is alive when the helper call can throw, but the second guard
is constructed only after that call returns. The exceptional path must destroy
only the first guard; the normal path constructs and destroys both guards.

```cpp filename=guarded_before_second.cpp function=guarded_before_second profile=scalar_int32
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

int guarded_before_second(int& first_cell, int& second_cell, bool should_throw) {
    try {
        Restore first(&first_cell);
        helper(should_throw);
        Restore second(&second_cell);
    } catch (int caught) {
        return first_cell;
    }
    return first_cell;
}
```

```click
verifying "guarded_before_second.cpp";

Restore::Restore(int32* slot) {
    owns this->pointer;
    owns this->saved;
    owns slot[0..1];
    ensures this->pointer == slot;
    ensures this->saved == old(slot[0]);
    ensures slot[0] == 9;
    ensures separate(memory(*this), memory(this->pointer[0..1]));
} by {
    step_until(function.exit);
    close();
}

Restore::~Restore() {
    requires separate(memory(*this), memory(this->pointer[0..1]));
    owns this->pointer;
    owns this->saved;
    owns this->pointer[0..1];
    ensures this->pointer == old(this->pointer);
    ensures this->saved == old(this->saved);
    ensures this->pointer[0] == old(this->saved);
} by {
    step_until(function.exit);
    close();
}

int32 helper(bool should_throw) throws int32 {
    ensures result == 5;
    exceptional ensures exception == 7;
}

int32 guarded_before_second(
    int32& first_cell,
    int32& second_cell,
    bool should_throw
) {
    owns first_cell;
    owns second_cell;
    requires separate(memory(first_cell), memory(second_cell));
    ensures result == old(first_cell);
    ensures first_cell == old(first_cell);
    ensures second_cell == old(second_cell);
} by {
    step();
    step();
    outcomes {
        returned => {
            step();
            step();
            step();
            have second_cell == old(second_cell);
            step_until(function.exit);
            close();
        }
        threw => {
            have second_cell == old(second_cell);
            step_until(function.exit);
            close();
        }
    }
}
```

```expect
pass
```
